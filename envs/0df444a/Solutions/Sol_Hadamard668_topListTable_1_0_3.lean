-- Prove2me | solution 1 for Hadamard668.topListTable_1_0_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:20:07.916079+00:00
-- url     : https://prove2.me/submissions/f3b4b23b-f66e-4c88-bb27-6441516425ce

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
    topListTable 1 0 3 = topExpectedTable 1 0 3 := by
  decide
end Hadamard668
