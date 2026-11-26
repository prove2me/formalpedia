-- Prove2me | solution 1 for Hadamard668.topListTable_3_0_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:57.501157+00:00
-- url     : https://prove2.me/submissions/5c6e2b46-e234-48d0-9d4f-d72af01f3026

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
    topListTable 3 0 3 = topExpectedTable 3 0 3 := by
  decide
end Hadamard668
