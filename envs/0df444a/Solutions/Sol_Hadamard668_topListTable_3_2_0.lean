-- Prove2me | solution 1 for Hadamard668.topListTable_3_2_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:25:47.374844+00:00
-- url     : https://prove2.me/submissions/5647ff1d-fe0e-4e19-9cd5-26e29049d915

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
    topListTable 3 2 0 = topExpectedTable 3 2 0 := by
  decide
end Hadamard668
