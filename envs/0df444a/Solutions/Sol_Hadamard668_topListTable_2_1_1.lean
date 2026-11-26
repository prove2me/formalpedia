-- Prove2me | solution 1 for Hadamard668.topListTable_2_1_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:23:24.447731+00:00
-- url     : https://prove2.me/submissions/ba4a7426-3a67-4510-a581-bb2831577062

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
    topListTable 2 1 1 = topExpectedTable 2 1 1 := by
  decide
end Hadamard668
