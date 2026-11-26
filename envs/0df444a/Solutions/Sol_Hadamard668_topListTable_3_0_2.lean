-- Prove2me | solution 1 for Hadamard668.topListTable_3_0_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:24:39.368804+00:00
-- url     : https://prove2.me/submissions/c7189958-d46d-4961-873d-4a3a37f6e73d

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
    topListTable 3 0 2 = topExpectedTable 3 0 2 := by
  decide
end Hadamard668
