-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:13:33.264865+00:00
-- url     : https://prove2.me/submissions/ddf29a42-e4f3-4876-9b07-6cb8a711509d

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
    baseListTable 3 0 2 true = baseExpectedTable 3 0 2 true := by
  decide
end Hadamard668
