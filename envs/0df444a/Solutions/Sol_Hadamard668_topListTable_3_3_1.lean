-- Prove2me | solution 1 for Hadamard668.topListTable_3_3_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:26:25.192652+00:00
-- url     : https://prove2.me/submissions/3698959a-1627-42b9-aab0-9ff82550c7e3

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
    topListTable 3 3 1 = topExpectedTable 3 3 1 := by
  decide
end Hadamard668
