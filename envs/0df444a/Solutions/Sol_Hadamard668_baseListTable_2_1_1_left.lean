-- Prove2me | solution 1 for Hadamard668.baseListTable_2_1_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:09:22.408879+00:00
-- url     : https://prove2.me/submissions/dfa20f16-d77e-43ca-ba28-bf18e30e9f9c

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
    baseListTable 2 1 1 false = baseExpectedTable 2 1 1 false := by
  decide
end Hadamard668
