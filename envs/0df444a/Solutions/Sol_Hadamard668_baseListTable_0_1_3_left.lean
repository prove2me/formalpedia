-- Prove2me | solution 1 for Hadamard668.baseListTable_0_1_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:59:42.282806+00:00
-- url     : https://prove2.me/submissions/43948208-8f65-46c5-a813-6d687cd57996

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
    baseListTable 0 1 3 false = baseExpectedTable 0 1 3 false := by
  decide
end Hadamard668
