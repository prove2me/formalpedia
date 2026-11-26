-- Prove2me | solution 1 for Hadamard668.baseListTable_2_3_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:12:38.212795+00:00
-- url     : https://prove2.me/submissions/7e26d78c-9b08-4dfb-ab4a-798193074d08

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
    baseListTable 2 3 2 true = baseExpectedTable 2 3 2 true := by
  decide
end Hadamard668
