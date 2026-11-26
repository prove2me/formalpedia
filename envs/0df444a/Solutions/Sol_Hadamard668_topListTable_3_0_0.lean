-- Prove2me | solution 1 for Hadamard668.topListTable_3_0_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:35.294384+00:00
-- url     : https://prove2.me/submissions/88a0604e-e1f6-4f7a-8d9e-0a32292cf531

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
    topListTable 3 0 0 = topExpectedTable 3 0 0 := by
  decide
end Hadamard668
