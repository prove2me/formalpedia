-- Prove2me | solution 1 for Hadamard668.baseListTable_1_3_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:07:08.001986+00:00
-- url     : https://prove2.me/submissions/7c5a8044-9d1b-4ac8-86ab-aeb3c3119643

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
    baseListTable 1 3 2 true = baseExpectedTable 1 3 2 true := by
  decide
end Hadamard668
