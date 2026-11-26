-- Prove2me | solution 1 for Hadamard668.topListTable_0_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:23.114533+00:00
-- url     : https://prove2.me/submissions/3f1c7f38-bc79-4cae-9fb6-c6173501acc9

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
    topListTable 0 1 3 = topExpectedTable 0 1 3 := by
  decide
end Hadamard668
