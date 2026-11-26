-- Prove2me | solution 1 for Hadamard668.baseListTable_2_1_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:10:09.545311+00:00
-- url     : https://prove2.me/submissions/77b50805-d337-4811-8233-e543c16d9a0a

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
    baseListTable 2 1 3 true = baseExpectedTable 2 1 3 true := by
  decide
end Hadamard668
