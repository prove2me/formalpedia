-- Prove2me | solution 1 for Hadamard668.baseListTable_2_2_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:10:38.846348+00:00
-- url     : https://prove2.me/submissions/ea82c01c-ee23-4625-b6f4-376eae1ff54f

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
    baseListTable 2 2 1 false = baseExpectedTable 2 2 1 false := by
  decide
end Hadamard668
