-- Prove2me | solution 1 for Hadamard668.baseListTable_0_1_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:59:00.084574+00:00
-- url     : https://prove2.me/submissions/f8c26042-4c44-435a-ac2e-c6971a0223da

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
    baseListTable 0 1 0 true = baseExpectedTable 0 1 0 true := by
  decide
end Hadamard668
