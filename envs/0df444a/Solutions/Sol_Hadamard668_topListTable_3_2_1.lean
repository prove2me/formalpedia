-- Prove2me | solution 1 for Hadamard668.topListTable_3_2_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:25:51.307787+00:00
-- url     : https://prove2.me/submissions/794e90b5-5098-452b-8b13-5a0388af2598

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
    topListTable 3 2 1 = topExpectedTable 3 2 1 := by
  decide
end Hadamard668
