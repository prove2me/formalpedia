-- Prove2me | solution 1 for Hadamard668.baseListTable_1_0_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:02:26.712311+00:00
-- url     : https://prove2.me/submissions/a2ad9def-4a27-4b5e-9ba8-9c773c940fe7

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
    baseListTable 1 0 0 true = baseExpectedTable 1 0 0 true := by
  decide
end Hadamard668
