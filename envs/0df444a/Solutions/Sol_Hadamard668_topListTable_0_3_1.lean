-- Prove2me | solution 1 for Hadamard668.topListTable_0_3_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:19:31.436796+00:00
-- url     : https://prove2.me/submissions/7855ec88-19ed-430e-9485-bd80fbd01116

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
    topListTable 0 3 1 = topExpectedTable 0 3 1 := by
  decide
end Hadamard668
