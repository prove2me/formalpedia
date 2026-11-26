-- Prove2me | solution 1 for Hadamard668.topListTable_0_0_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:10.966606+00:00
-- url     : https://prove2.me/submissions/f800980c-528d-42f8-ac1a-3948ecc603ad

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
    topListTable 0 0 2 = topExpectedTable 0 0 2 := by
  decide
end Hadamard668
