-- Prove2me | solution 1 for Hadamard668.baseListTable_0_3_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:01:50.501732+00:00
-- url     : https://prove2.me/submissions/a6a014b0-a1ae-44c7-814a-a551c6fad211

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
    baseListTable 0 3 1 true = baseExpectedTable 0 3 1 true := by
  decide
end Hadamard668
