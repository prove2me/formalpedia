-- Prove2me | solution 1 for Hadamard668.baseListTable_3_2_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:16:16.723497+00:00
-- url     : https://prove2.me/submissions/8efb5a7b-1ddf-4bae-9396-3eadbefc3426

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
    baseListTable 3 2 3 true = baseExpectedTable 3 2 3 true := by
  decide
end Hadamard668
