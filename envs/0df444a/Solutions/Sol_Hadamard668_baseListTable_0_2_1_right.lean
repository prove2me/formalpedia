-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:28.870297+00:00
-- url     : https://prove2.me/submissions/0009bf3b-5c04-4584-97af-a7d35f16ed44

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
    baseListTable 0 2 1 true = baseExpectedTable 0 2 1 true := by
  decide
end Hadamard668
