-- Prove2me | solution 1 for Hadamard668.baseListTable_3_3_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:16:46.733347+00:00
-- url     : https://prove2.me/submissions/4f34aabd-54ff-4356-a0b2-f9eb9a28c649

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
    baseListTable 3 3 1 true = baseExpectedTable 3 3 1 true := by
  decide
end Hadamard668
