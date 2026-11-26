-- Prove2me | solution 1 for Hadamard668.baseListTable_1_3_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:06:41.276552+00:00
-- url     : https://prove2.me/submissions/741a0fe4-3344-476c-aeb5-5c4ccac16292

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
    baseListTable 1 3 1 false = baseExpectedTable 1 3 1 false := by
  decide
end Hadamard668
