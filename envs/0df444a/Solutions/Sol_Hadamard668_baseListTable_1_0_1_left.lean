-- Prove2me | solution 1 for Hadamard668.baseListTable_1_0_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:03:09.907392+00:00
-- url     : https://prove2.me/submissions/c012eb28-5da9-4efe-a7a2-ac47de3da0d2

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
    baseListTable 1 0 1 false = baseExpectedTable 1 0 1 false := by
  decide
end Hadamard668
