-- Prove2me | solution 1 for Hadamard668.baseListTable_3_2_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:16:05.101349+00:00
-- url     : https://prove2.me/submissions/a419f0fd-1b79-4b41-859f-cc4b7d5c02ee

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
    baseListTable 3 2 2 true = baseExpectedTable 3 2 2 true := by
  decide
end Hadamard668
