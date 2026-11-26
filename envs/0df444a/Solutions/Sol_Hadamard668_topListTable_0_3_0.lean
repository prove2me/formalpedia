-- Prove2me | solution 1 for Hadamard668.topListTable_0_3_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:19:22.512819+00:00
-- url     : https://prove2.me/submissions/22cf3793-e709-427b-85f4-a0527ac7c408

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
    topListTable 0 3 0 = topExpectedTable 0 3 0 := by
  decide
end Hadamard668
