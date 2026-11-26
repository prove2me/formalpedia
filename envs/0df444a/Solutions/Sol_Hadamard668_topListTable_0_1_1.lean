-- Prove2me | solution 1 for Hadamard668.topListTable_0_1_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:21.159942+00:00
-- url     : https://prove2.me/submissions/dc3a459c-cb8e-4f19-b179-be5a20310117

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
    topListTable 0 1 1 = topExpectedTable 0 1 1 := by
  decide
end Hadamard668
