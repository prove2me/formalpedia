-- Prove2me | solution 1 for Hadamard668.baseListTable_2_1_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:09:04.687942+00:00
-- url     : https://prove2.me/submissions/144f188c-5e76-4cd7-b303-5fba27ab1e8f

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
    baseListTable 2 1 0 false = baseExpectedTable 2 1 0 false := by
  decide
end Hadamard668
