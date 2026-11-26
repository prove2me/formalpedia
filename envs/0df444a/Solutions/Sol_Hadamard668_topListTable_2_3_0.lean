-- Prove2me | solution 1 for Hadamard668.topListTable_2_3_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:02.444872+00:00
-- url     : https://prove2.me/submissions/c6ec58eb-b618-41de-ae8a-1865444b8d15

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
    topListTable 2 3 0 = topExpectedTable 2 3 0 := by
  decide
end Hadamard668
