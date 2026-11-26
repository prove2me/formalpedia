-- Prove2me | solution 1 for Hadamard668.baseListTable_3_3_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:16:43.738229+00:00
-- url     : https://prove2.me/submissions/72593fcb-a63b-4034-8b15-6b09e6b0fe05

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
    baseListTable 3 3 1 false = baseExpectedTable 3 3 1 false := by
  decide
end Hadamard668
