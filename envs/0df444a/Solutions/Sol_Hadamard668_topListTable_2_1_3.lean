-- Prove2me | solution 1 for Hadamard668.topListTable_2_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:23:27.513065+00:00
-- url     : https://prove2.me/submissions/1d7960ac-e9dc-44e5-b7e0-b938a376903e

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
    topListTable 2 1 3 = topExpectedTable 2 1 3 := by
  decide
end Hadamard668
