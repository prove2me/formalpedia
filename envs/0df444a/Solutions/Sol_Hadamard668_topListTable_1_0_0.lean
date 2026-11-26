-- Prove2me | solution 1 for Hadamard668.topListTable_1_0_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:19:53.83781+00:00
-- url     : https://prove2.me/submissions/f1fd298f-e673-41f1-8ecc-aed01567f74d

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
    topListTable 1 0 0 = topExpectedTable 1 0 0 := by
  decide
end Hadamard668
