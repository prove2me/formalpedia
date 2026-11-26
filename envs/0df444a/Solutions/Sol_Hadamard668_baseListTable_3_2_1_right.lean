-- Prove2me | solution 1 for Hadamard668.baseListTable_3_2_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:15:46.885788+00:00
-- url     : https://prove2.me/submissions/21f72a46-5da1-46b8-8b09-51e1d7d75dd0

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
    baseListTable 3 2 1 true = baseExpectedTable 3 2 1 true := by
  decide
end Hadamard668
