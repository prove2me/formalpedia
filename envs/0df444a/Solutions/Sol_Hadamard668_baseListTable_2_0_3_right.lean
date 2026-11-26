-- Prove2me | solution 1 for Hadamard668.baseListTable_2_0_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:09:00.437216+00:00
-- url     : https://prove2.me/submissions/e489ed4d-f6b5-4823-9984-82bb5d554e50

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
    baseListTable 2 0 3 true = baseExpectedTable 2 0 3 true := by
  decide
end Hadamard668
