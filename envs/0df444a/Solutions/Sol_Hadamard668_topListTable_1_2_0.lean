-- Prove2me | solution 1 for Hadamard668.topListTable_1_2_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:21:07.180509+00:00
-- url     : https://prove2.me/submissions/b2e3bc98-6a7b-42fe-a073-de73bd31740b

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
    topListTable 1 2 0 = topExpectedTable 1 2 0 := by
  decide
end Hadamard668
