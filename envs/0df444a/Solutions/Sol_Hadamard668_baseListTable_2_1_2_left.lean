-- Prove2me | solution 1 for Hadamard668.baseListTable_2_1_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:09:36.37483+00:00
-- url     : https://prove2.me/submissions/41ae8e63-2bd6-482a-abf1-8e2f7060cf68

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
    baseListTable 2 1 2 false = baseExpectedTable 2 1 2 false := by
  decide
end Hadamard668
