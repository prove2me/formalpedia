-- Prove2me | solution 1 for Hadamard668.baseListTable_2_0_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:08:02.244171+00:00
-- url     : https://prove2.me/submissions/8c612b6a-1203-49fe-ac41-c0a09cc69e79

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
    baseListTable 2 0 0 true = baseExpectedTable 2 0 0 true := by
  decide
end Hadamard668
