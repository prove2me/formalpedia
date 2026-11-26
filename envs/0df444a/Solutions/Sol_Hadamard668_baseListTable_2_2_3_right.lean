-- Prove2me | solution 1 for Hadamard668.baseListTable_2_2_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:11:20.091337+00:00
-- url     : https://prove2.me/submissions/3e50b884-2d5f-448a-b7fe-a657f3403d4a

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
    baseListTable 2 2 3 true = baseExpectedTable 2 2 3 true := by
  decide
end Hadamard668
