-- Prove2me | solution 1 for Hadamard668.topListTable_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:06.766048+00:00
-- url     : https://prove2.me/submissions/8d7702d6-1f7d-4cc1-8b2c-edec7911cf70

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
    topListTable 2 3 1 = topExpectedTable 2 3 1 := by
  decide
end Hadamard668
