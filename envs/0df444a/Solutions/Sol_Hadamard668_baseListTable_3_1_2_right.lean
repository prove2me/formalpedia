-- Prove2me | solution 1 for Hadamard668.baseListTable_3_1_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:14:33.487734+00:00
-- url     : https://prove2.me/submissions/651aa166-bef1-45cd-8089-a315425cd5f6

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
    baseListTable 3 1 2 true = baseExpectedTable 3 1 2 true := by
  decide
end Hadamard668
