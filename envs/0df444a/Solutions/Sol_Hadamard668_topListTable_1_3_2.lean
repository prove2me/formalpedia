-- Prove2me | solution 1 for Hadamard668.topListTable_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:22:00.008924+00:00
-- url     : https://prove2.me/submissions/778cd624-8336-42b2-9ef4-6e52e4fcb563

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
    topListTable 1 3 2 = topExpectedTable 1 3 2 := by
  decide
end Hadamard668
