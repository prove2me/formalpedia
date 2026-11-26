-- Prove2me | solution 1 for Hadamard668.baseListTable_1_2_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:05:27.248858+00:00
-- url     : https://prove2.me/submissions/a1657536-0811-48a0-b3fc-3f6cdd9a55d1

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
    baseListTable 1 2 0 true = baseExpectedTable 1 2 0 true := by
  decide
end Hadamard668
