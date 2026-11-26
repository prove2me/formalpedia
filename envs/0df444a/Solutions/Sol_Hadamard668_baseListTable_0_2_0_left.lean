-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:59:47.093908+00:00
-- url     : https://prove2.me/submissions/8b4e40cb-e71c-448c-a5a7-481eef4571e7

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
    baseListTable 0 2 0 false = baseExpectedTable 0 2 0 false := by
  decide
end Hadamard668
