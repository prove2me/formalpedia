-- Prove2me | solution 1 for Hadamard668.topListTable_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:21:38.728598+00:00
-- url     : https://prove2.me/submissions/3a3b858a-eee8-4ccd-9a1b-bdd678bc6569

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
    topListTable 1 3 0 = topExpectedTable 1 3 0 := by
  decide
end Hadamard668
