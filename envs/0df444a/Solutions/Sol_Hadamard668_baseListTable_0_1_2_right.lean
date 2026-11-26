-- Prove2me | solution 1 for Hadamard668.baseListTable_0_1_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:59:41.696134+00:00
-- url     : https://prove2.me/submissions/dc96b9c0-bf0f-431e-81da-aadd6bb93b66

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
    baseListTable 0 1 2 true = baseExpectedTable 0 1 2 true := by
  decide
end Hadamard668
