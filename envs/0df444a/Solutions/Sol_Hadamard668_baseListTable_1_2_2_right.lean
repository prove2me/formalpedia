-- Prove2me | solution 1 for Hadamard668.baseListTable_1_2_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:05:37.873519+00:00
-- url     : https://prove2.me/submissions/fb354a97-8881-4787-a72b-2f7a8242ba8e

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
    baseListTable 1 2 2 true = baseExpectedTable 1 2 2 true := by
  decide
end Hadamard668
