-- Prove2me | solution 1 for Hadamard668.topListTable_3_1_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:25:29.854049+00:00
-- url     : https://prove2.me/submissions/73cf5b4c-fc06-4d3b-be44-f1c6fa237845

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
    topListTable 3 1 1 = topExpectedTable 3 1 1 := by
  decide
end Hadamard668
