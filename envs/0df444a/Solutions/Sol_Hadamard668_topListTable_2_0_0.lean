-- Prove2me | solution 1 for Hadamard668.topListTable_2_0_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:22:17.772699+00:00
-- url     : https://prove2.me/submissions/54d3041a-f5d2-441e-a398-5544861c9196

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
    topListTable 2 0 0 = topExpectedTable 2 0 0 := by
  decide
end Hadamard668
