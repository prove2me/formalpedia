-- Prove2me | solution 1 for Hadamard668.baseListTable_1_1_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:03:44.43857+00:00
-- url     : https://prove2.me/submissions/f9718ca6-ed42-4207-a2b9-8d1aa7bf9338

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
    baseListTable 1 1 0 true = baseExpectedTable 1 1 0 true := by
  decide
end Hadamard668
