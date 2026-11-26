-- Prove2me | solution 1 for Hadamard668.topListTable_0_3_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:19:32.170999+00:00
-- url     : https://prove2.me/submissions/32861a59-3d91-42c2-902d-c14c1f88c24a

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
    topListTable 0 3 2 = topExpectedTable 0 3 2 := by
  decide
end Hadamard668
