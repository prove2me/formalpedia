-- Prove2me | solution 1 for Hadamard668.topListTable_0_0_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:08.900178+00:00
-- url     : https://prove2.me/submissions/206495df-9d36-4083-bc26-5c740207ecb4

import Definitions.Def_Hadamard668_CertificateData
import Definitions.Def_Hadamard668_CorrelationData
import Mathlib
import Definitions.Def_Hadamard668_ListCorrelationProof

set_option autoImplicit true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Hadamard668
namespace Hadamard668
theorem _root_.solution :
    topListTable 0 0 1 = topExpectedTable 0 0 1 := by
  decide
end Hadamard668
