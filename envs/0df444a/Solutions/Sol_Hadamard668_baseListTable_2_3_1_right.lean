-- Prove2me | solution 1 for Hadamard668.baseListTable_2_3_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:12:00.722282+00:00
-- url     : https://prove2.me/submissions/0f2d4a66-3818-4711-8ede-967d81410e93

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
    baseListTable 2 3 1 true = baseExpectedTable 2 3 1 true := by
  decide
end Hadamard668
