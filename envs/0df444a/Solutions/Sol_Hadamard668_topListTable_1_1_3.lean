-- Prove2me | solution 1 for Hadamard668.topListTable_1_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:21:05.490889+00:00
-- url     : https://prove2.me/submissions/01ec55dc-a249-413c-beb4-1b34696b0b7c

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
    topListTable 1 1 3 = topExpectedTable 1 1 3 := by
  decide
end Hadamard668
