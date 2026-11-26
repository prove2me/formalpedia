-- Prove2me | solution 1 for Hadamard668.topListTable_2_0_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:22:18.673189+00:00
-- url     : https://prove2.me/submissions/9da59b15-0d36-4ef6-8363-579913014d8a

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
    topListTable 2 0 2 = topExpectedTable 2 0 2 := by
  decide
end Hadamard668
