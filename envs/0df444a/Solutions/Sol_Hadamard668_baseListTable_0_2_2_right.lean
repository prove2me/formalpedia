-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:53.651831+00:00
-- url     : https://prove2.me/submissions/ccfb58fe-f7d4-493a-8bfe-6c5f84d2706e

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
    baseListTable 0 2 2 true = baseExpectedTable 0 2 2 true := by
  decide
end Hadamard668
