/** Common command line processing for benchmarks -*- C++ -*-
 * @file
 * @section License
 *
 * This file is part of Galois.  Galois is a framework to exploit
 * amorphous data-parallelism in irregular programs.
 *
 * Galois is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * Galois is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Galois.  If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * @section Copyright
 *
 * Copyright (C) 2017, The University of Texas at Austin. All rights
 * reserved.
 *
 * @section Description
 *
 * Perform common setup tasks for the distributed benchmarks + contains 
 * initialization functions for said benchmarks
 *
 * @author Gurbinder Gill <gill@cs.utexas.edu>
 * @author Loc Hoang <l_hoang@utexas.edu>
 */

#include "DistBenchStart.h"
#include "galois/Version.h"
#include "galois/runtime/Network.h"
#include "galois/runtime/DistStats.h"
#include "galois/runtime/DataCommMode.h"

#include <iostream>
#include <sstream>

////////////////////////////////////////////////////////////////////////////////
// Command line args
////////////////////////////////////////////////////////////////////////////////

cll::opt<int> numThreads("t", cll::desc("Number of threads"), 
                              cll::init(1));
cll::opt<int> numRuns("runs", cll::desc("Number of runs"), 
                              cll::init(3));
cll::opt<std::string> statFile("statFile", 
         cll::desc("output file to print stats to "), 
         cll::init(""));
cll::opt<unsigned int> enforce_metadata("metadata", 
          cll::desc("Enforce communication metadata: 0 - auto (default), "
                         "1 - bitset, 2 - indices, 3 - no metadata"), 
          cll::init(0));
cll::opt<bool> verify("verify", 
                     cll::desc("Verify results by outputting results to file"), 
                     cll::init(false));

#ifdef __GALOIS_HET_CUDA__
std::string personality_str(Personality p) {
  switch (p) {
    case CPU:
      return "CPU";
    case GPU_CUDA:
      return "GPU_CUDA";
    case GPU_OPENCL:
      return "GPU_OPENCL";
  }

  assert(false && "Invalid personality");
  return "";
}

cll::opt<int> gpudevice("gpu", cll::desc("Select GPU to run on, "
                                         "default is to choose automatically"), 
                               cll::init(-1));
cll::opt<Personality> personality("personality", cll::desc("Personality"),
      cll::values(clEnumValN(CPU, "cpu", "Galois CPU"), 
                  clEnumValN(GPU_CUDA, "gpu/cuda", "GPU/CUDA"), 
                  clEnumValN(GPU_OPENCL, "gpu/opencl", "GPU/OpenCL"), 
                  clEnumValEnd),
      cll::init(CPU));
cll::opt<unsigned> scalegpu("scalegpu", 
      cll::desc("Scale GPU workload w.r.t. CPU, default is proportionally "
                "equal workload to CPU and GPU (1)"), 
      cll::init(1));
cll::opt<unsigned> scalecpu("scalecpu", 
      cll::desc("Scale CPU workload w.r.t. GPU, default is proportionally "
                "equal workload to CPU and GPU (1)"), 
      cll::init(1));
cll::opt<int> num_nodes("num_nodes", 
      cll::desc("Num of physical nodes with devices (default = num of hosts): " 
                "detect GPU to use for each host automatically"), 
      cll::init(-1));
cll::opt<std::string> personality_set("pset", 
      cll::desc("String specifying personality for hosts on each physical "
                "node. 'c'=CPU,'g'=GPU/CUDA and 'o'=GPU/OpenCL"), 
      cll::init("c"));
#endif

DataCommMode enforce_data_mode = noData;

static void PrintVersion() {
  std::cout << "Galois Benchmark Suite v" << galois::getVersion() << " (" 
            << galois::getRevision() << ")\n";
}

////////////////////////////////////////////////////////////////////////////////
//! initialize benchmark + functions to help initialization
////////////////////////////////////////////////////////////////////////////////

void DistBenchStart(int argc, char** argv, const char* app, const char* desc, 
                    const char* url) {
  llvm::cl::SetVersionPrinter(PrintVersion);
  llvm::cl::ParseCommandLineOptions(argc, argv);
  numThreads = galois::setActiveThreads(numThreads); 
  galois::runtime::setStatFile(statFile);

  assert(enforce_metadata <= 3);
  enforce_data_mode = static_cast<DataCommMode>((unsigned int)enforce_metadata);

  auto& net = galois::runtime::getSystemNetworkInterface();
  
  if (net.ID == 0) {
    PrintVersion();
    std::cout << "Copyright (C) " << galois::getCopyrightYear() 
              << " The University of Texas at Austin\n";
    std::cout << "http://iss.ices.utexas.edu/galois/\n\n";
    std::cout << "application: " <<  (app ? app : "unspecified") << "\n";

    if (desc) {
      std::cout << desc << "\n";
    }
    if (url) {
      std::cout << "http://iss.ices.utexas.edu/?p=projects/galois/benchmarks/" 
                << url << "\n";
    }
    std::cout << "\n";

    std::ostringstream cmdout;

    for (int i = 0; i < argc; ++i) {
      cmdout << argv[i];
      if (i != argc - 1)
        cmdout << " ";
    }

    galois::runtime::reportParam("DistBench", "CommandLine", cmdout.str());
    galois::runtime::reportParam("DistBench", "Threads", 
                                 (unsigned long)numThreads);
    galois::runtime::reportParam("DistBench", "Hosts", (unsigned long)net.Num);
    galois::runtime::reportParam("DistBench", "Runs", (unsigned long)numRuns);
    galois::runtime::reportParam("DistBench", "Run_UUID", 
                                 galois::runtime::getRandUUID());
    galois::runtime::reportParam("DistBench", "Input", 
                                   inputFile);
    galois::runtime::reportParam("DistBench", "PartitionScheme", 
                                   EnumToString(partitionScheme));
  }

  char name[256];
  gethostname(name, 256);
  galois::runtime::reportParam("DistBench", "Hostname", name);
}

#ifdef __GALOIS_HET_CUDA__
/**
 * Processes/setups the specified heterogeneous configuration (the pset
 * command line option) and sets up the scale factor vector for
 * graph partitioning.
 * 
 * @param scaleFactor input and output: an empty vector that will hold
 * the scale factor (i.e. how much each host will get relative to
 * other hosts) at the end of the function
 */
void internal::heteroSetup(std::vector<unsigned>& scaleFactor) {
  const unsigned my_host_id = galois::runtime::getHostID();

  // Parse arg string when running on multiple hosts and update/override 
  // personality with corresponding value.
  auto& net = galois::runtime::getSystemNetworkInterface();

  if (num_nodes == -1) num_nodes = net.Num;

  assert((net.Num % num_nodes) == 0);

  if (personality_set.length() == (net.Num / num_nodes)) {
    switch (personality_set.c_str()[my_host_id % (net.Num / num_nodes)]) {
      case 'g':
        personality = GPU_CUDA;
        break;
      case 'o':
        assert(0);
        personality = GPU_OPENCL;
        break;
      case 'c':
      default:
        personality = CPU;
        break;
    }

    if ((personality == GPU_CUDA) && (gpudevice == -1)) {
      gpudevice = get_gpu_device_id(personality_set, num_nodes);
    }

    // scale factor setup
    if ((scalecpu > 1) || (scalegpu > 1)) {
      for (unsigned i = 0; i < net.Num; ++i) {
        if (personality_set.c_str()[i % num_nodes] == 'c') {
          scaleFactor.push_back(scalecpu);
        } else {
          scaleFactor.push_back(scalegpu);
        }
      }
    }
  }
}
#endif
