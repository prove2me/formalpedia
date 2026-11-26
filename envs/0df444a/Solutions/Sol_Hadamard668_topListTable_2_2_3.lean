-- Prove2me | solution 1 for Hadamard668.topListTable_2_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:23:53.603862+00:00
-- url     : https://prove2.me/submissions/e4f092d4-6201-412e-9e48-b9351fccd096

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
    topListTable 2 2 3 = topExpectedTable 2 2 3 := by
  decide
end Hadamard668
