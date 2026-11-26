-- Prove2me | solution 1 for Hadamard668.baseListTable_3_2_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:15:46.082487+00:00
-- url     : https://prove2.me/submissions/47f31165-6d71-4bc2-8353-7c270f868a2f

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
    baseListTable 3 2 1 false = baseExpectedTable 3 2 1 false := by
  decide
end Hadamard668
