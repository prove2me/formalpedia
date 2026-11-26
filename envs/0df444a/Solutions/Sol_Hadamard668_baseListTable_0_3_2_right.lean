-- Prove2me | solution 1 for Hadamard668.baseListTable_0_3_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:01:59.13153+00:00
-- url     : https://prove2.me/submissions/8659dc02-0fca-42b2-9746-7e9d964d14ab

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
    baseListTable 0 3 2 true = baseExpectedTable 0 3 2 true := by
  decide
end Hadamard668
