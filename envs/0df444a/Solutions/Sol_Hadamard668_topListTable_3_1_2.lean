-- Prove2me | solution 1 for Hadamard668.topListTable_3_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:25:39.915286+00:00
-- url     : https://prove2.me/submissions/8026a951-f4e2-44c0-b59b-5d1f56eabe9b

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
    topListTable 3 1 2 = topExpectedTable 3 1 2 := by
  decide
end Hadamard668
