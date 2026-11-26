-- Prove2me | solution 1 for Hadamard668.topListTable_3_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:25:40.807335+00:00
-- url     : https://prove2.me/submissions/502d04ac-cb33-4ecd-83ff-524247f06693

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
    topListTable 3 1 3 = topExpectedTable 3 1 3 := by
  decide
end Hadamard668
