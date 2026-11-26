-- Prove2me | solution 1 for Hadamard668.topListTable_1_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:21:34.670821+00:00
-- url     : https://prove2.me/submissions/2f504e1b-b6c1-49ef-9754-cf6725328d31

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
    topListTable 1 2 3 = topExpectedTable 1 2 3 := by
  decide
end Hadamard668
