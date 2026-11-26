-- Prove2me | solution 1 for Hadamard668.topListTable_0_2_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:18:31.251686+00:00
-- url     : https://prove2.me/submissions/3ecb1712-a2ed-42dd-af2f-b196414efa80

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
    topListTable 0 2 1 = topExpectedTable 0 2 1 := by
  decide
end Hadamard668
