-- Prove2me | solution 1 for Hadamard668.topListTable_0_3_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:19:50.089666+00:00
-- url     : https://prove2.me/submissions/6170a2cd-b185-48f2-9e54-76003bc685a3

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
    topListTable 0 3 3 = topExpectedTable 0 3 3 := by
  decide
end Hadamard668
