-- Prove2me | solution 1 for Hadamard668.topListTable_3_0_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:38.565521+00:00
-- url     : https://prove2.me/submissions/0da70b36-d4d3-421d-9d08-e6dc4d6c905b

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
    topListTable 3 0 1 = topExpectedTable 3 0 1 := by
  decide
end Hadamard668
