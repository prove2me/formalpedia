-- Prove2me | solution 1 for Hadamard668.topListTable_2_3_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:07.663735+00:00
-- url     : https://prove2.me/submissions/b5ff7a79-688d-4701-b2a4-51ac5def51e8

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
    topListTable 2 3 2 = topExpectedTable 2 3 2 := by
  decide
end Hadamard668
