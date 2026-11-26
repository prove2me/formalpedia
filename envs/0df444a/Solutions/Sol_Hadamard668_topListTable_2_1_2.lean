-- Prove2me | solution 1 for Hadamard668.topListTable_2_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:23:26.929881+00:00
-- url     : https://prove2.me/submissions/aef451d1-846e-4275-be31-a5a974b444c1

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
    topListTable 2 1 2 = topExpectedTable 2 1 2 := by
  decide
end Hadamard668
