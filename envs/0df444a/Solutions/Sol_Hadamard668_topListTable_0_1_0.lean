-- Prove2me | solution 1 for Hadamard668.topListTable_0_1_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:20.623278+00:00
-- url     : https://prove2.me/submissions/2770f37e-61d4-45f8-92b1-b2a5d7872cb6

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
    topListTable 0 1 0 = topExpectedTable 0 1 0 := by
  decide
end Hadamard668
