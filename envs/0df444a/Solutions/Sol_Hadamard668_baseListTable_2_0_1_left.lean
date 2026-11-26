-- Prove2me | solution 1 for Hadamard668.baseListTable_2_0_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:08:07.57754+00:00
-- url     : https://prove2.me/submissions/24340ec9-300f-412e-b7b5-89078ecab884

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
    baseListTable 2 0 1 false = baseExpectedTable 2 0 1 false := by
  decide
end Hadamard668
