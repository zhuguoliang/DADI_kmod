project("LSMTReadOnlyFile_in_C")
cmake_minimum_required(VERSION 2.6)

set(CMAKE_CXX_FLAG "-std=c++11")
set(CMAKE_C_FLAG "-std=c11")
#set(CMAKE_LINK_FLAGS "${CMAKE_LINK_FLAGS} -fprofile-instr-generate")
add_compile_options("-std=c++11")
add_compile_options("-lpthread")

if (CMAKE_BUILD_TYPE STREQUAL "Release")
	add_compile_options("-O3")
else()
	add_compile_options("-g")
	add_compile_options("-O0")
endif()

message("BUILD_TYPE: ${CMAKE_BUILD_TYPE}")

include_directories("./")
include_directories("./test")
include_directories("/opt/google/googletest/include")

set(SRC_LIST test/test.cc
	lsmt_ro_file.c
)

add_executable(test.bin ${SRC_LIST})

target_link_libraries(test.bin /opt/google/googletest/libgtest.a pthread)

