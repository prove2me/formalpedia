-- Prove2me | solution 1 for Hadamard668.baseListTable_2_0_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:08:20.947802+00:00
-- url     : https://prove2.me/submissions/1e065340-b5cd-458e-ba96-f3cfb8a09716

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
    baseListTable 2 0 1 true = baseExpectedTable 2 0 1 true := by
  decide
end Hadamard668
