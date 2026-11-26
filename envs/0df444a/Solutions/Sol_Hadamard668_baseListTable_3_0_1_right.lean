-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_1_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:13:14.504858+00:00
-- url     : https://prove2.me/submissions/35ad2a88-0eae-43dd-bf34-b71b3df65aae

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
    baseListTable 3 0 1 true = baseExpectedTable 3 0 1 true := by
  decide
end Hadamard668
