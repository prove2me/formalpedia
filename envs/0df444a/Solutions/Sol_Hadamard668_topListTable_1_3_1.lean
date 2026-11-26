-- Prove2me | solution 1 for Hadamard668.topListTable_1_3_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:21:54.713709+00:00
-- url     : https://prove2.me/submissions/eb43b1e0-8161-4766-b18e-66a12494277d

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
    topListTable 1 3 1 = topExpectedTable 1 3 1 := by
  decide
end Hadamard668
