-- Prove2me | solution 1 for Hadamard668.topListTable_2_1_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:22:44.818363+00:00
-- url     : https://prove2.me/submissions/c88a0395-6b44-4265-8634-cef45e24d50f

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
    topListTable 2 1 0 = topExpectedTable 2 1 0 := by
  decide
end Hadamard668
