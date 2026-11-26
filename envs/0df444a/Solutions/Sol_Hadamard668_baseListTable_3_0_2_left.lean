-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:13:21.95423+00:00
-- url     : https://prove2.me/submissions/eb59b954-198c-43b5-9d69-cd4a0db13dce

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
    baseListTable 3 0 2 false = baseExpectedTable 3 0 2 false := by
  decide
end Hadamard668
