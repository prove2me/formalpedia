-- Prove2me | solution 1 for Hadamard668.topListTable_1_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:20:32.935501+00:00
-- url     : https://prove2.me/submissions/a2e5e60d-d73b-4768-a9d6-e0513681fcbe

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
    topListTable 1 1 2 = topExpectedTable 1 1 2 := by
  decide
end Hadamard668
