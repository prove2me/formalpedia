-- Prove2me | solution 1 for Hadamard668.topListTable_1_0_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:20:03.874845+00:00
-- url     : https://prove2.me/submissions/86fa40c9-3ad5-4bb8-bf83-af0dbe861715

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
    topListTable 1 0 2 = topExpectedTable 1 0 2 := by
  decide
end Hadamard668
