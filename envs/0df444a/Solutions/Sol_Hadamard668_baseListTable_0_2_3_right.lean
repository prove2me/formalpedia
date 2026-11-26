-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:58.94384+00:00
-- url     : https://prove2.me/submissions/c2d935fb-51ba-4638-ab60-114e80e6ba6b

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
    baseListTable 0 2 3 true = baseExpectedTable 0 2 3 true := by
  decide
end Hadamard668
