-- Prove2me | solution 1 for Hadamard668.baseListTable_1_0_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:03:34.99863+00:00
-- url     : https://prove2.me/submissions/4927d102-3161-42d7-96af-d13a422fb980

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
    baseListTable 1 0 3 false = baseExpectedTable 1 0 3 false := by
  decide
end Hadamard668
