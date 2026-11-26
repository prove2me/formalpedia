-- Prove2me | solution 1 for Hadamard668.topListTable_1_1_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:20:19.561056+00:00
-- url     : https://prove2.me/submissions/268f827a-1ec6-4895-942a-66858979d2f9

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
    topListTable 1 1 0 = topExpectedTable 1 1 0 := by
  decide
end Hadamard668
