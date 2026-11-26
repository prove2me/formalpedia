-- Prove2me | solution 1 for Hadamard668.baseListTable_0_0_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:58:10.653802+00:00
-- url     : https://prove2.me/submissions/dd1d59ba-6e55-44a0-be58-526f226008a5

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
    baseListTable 0 0 1 true = baseExpectedTable 0 0 1 true := by
  decide
end Hadamard668
