-- Prove2me | solution 1 for Hadamard668.topListTable_0_2_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:30.764412+00:00
-- url     : https://prove2.me/submissions/ffaea610-bf72-4048-8253-3ab6c5e758a5

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
    topListTable 0 2 0 = topExpectedTable 0 2 0 := by
  decide
end Hadamard668
