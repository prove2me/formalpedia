-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:13:02.97083+00:00
-- url     : https://prove2.me/submissions/6d3fec18-cf01-4ff3-af30-789c1511b1dd

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
    baseListTable 3 0 0 true = baseExpectedTable 3 0 0 true := by
  decide
end Hadamard668
