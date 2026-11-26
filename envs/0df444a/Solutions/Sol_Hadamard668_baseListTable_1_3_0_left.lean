-- Prove2me | solution 1 for Hadamard668.baseListTable_1_3_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:06:39.808573+00:00
-- url     : https://prove2.me/submissions/3f4bb5f1-8487-4534-9cef-98d7231b5ca9

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
    baseListTable 1 3 0 false = baseExpectedTable 1 3 0 false := by
  decide
end Hadamard668
