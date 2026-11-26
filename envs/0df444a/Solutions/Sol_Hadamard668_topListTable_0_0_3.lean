-- Prove2me | solution 1 for Hadamard668.topListTable_0_0_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:11.717899+00:00
-- url     : https://prove2.me/submissions/c41bc36d-6189-4320-ad01-386b1a4c4217

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
    topListTable 0 0 3 = topExpectedTable 0 0 3 := by
  decide
end Hadamard668
