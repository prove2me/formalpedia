-- Prove2me | solution 1 for Hadamard668.baseListTable_1_0_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:03:36.154202+00:00
-- url     : https://prove2.me/submissions/783e3013-f666-4e09-b57c-c6909a174c26

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
    baseListTable 1 0 3 true = baseExpectedTable 1 0 3 true := by
  decide
end Hadamard668
