-- Prove2me | solution 1 for Hadamard668.baseListTable_1_2_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:05:31.743821+00:00
-- url     : https://prove2.me/submissions/aea64448-0f61-4d77-81be-4888a313d109

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
    baseListTable 1 2 1 true = baseExpectedTable 1 2 1 true := by
  decide
end Hadamard668
