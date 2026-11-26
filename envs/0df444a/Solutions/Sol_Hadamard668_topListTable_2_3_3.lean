-- Prove2me | solution 1 for Hadamard668.topListTable_2_3_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:27.824549+00:00
-- url     : https://prove2.me/submissions/2ff8551e-b0bd-4c2b-a883-84780cfac468

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
    topListTable 2 3 3 = topExpectedTable 2 3 3 := by
  decide
end Hadamard668
