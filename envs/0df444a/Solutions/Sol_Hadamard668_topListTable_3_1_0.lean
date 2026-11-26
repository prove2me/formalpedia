-- Prove2me | solution 1 for Hadamard668.topListTable_3_1_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:25:27.958534+00:00
-- url     : https://prove2.me/submissions/836bd323-6181-4f12-9727-65f9e53adc1c

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
    topListTable 3 1 0 = topExpectedTable 3 1 0 := by
  decide
end Hadamard668
