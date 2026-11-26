-- Prove2me | solution 1 for Hadamard668.baseListTable_1_3_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:06:40.421797+00:00
-- url     : https://prove2.me/submissions/118a6068-eeb9-4c95-9ee7-3afaa6d1c81b

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
    baseListTable 1 3 0 true = baseExpectedTable 1 3 0 true := by
  decide
end Hadamard668
