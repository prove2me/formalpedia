-- Prove2me | solution 1 for Hadamard668.topListTable_3_2_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:26:02.39521+00:00
-- url     : https://prove2.me/submissions/fe841f4d-55b2-4160-afd6-d5673cc4e90f

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
    topListTable 3 2 2 = topExpectedTable 3 2 2 := by
  decide
end Hadamard668
