-- Prove2me | solution 1 for Hadamard668.topListTable_0_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:19:21.368972+00:00
-- url     : https://prove2.me/submissions/923240e9-f7a4-4935-96aa-d3d741c4b0ed

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
    topListTable 0 2 3 = topExpectedTable 0 2 3 := by
  decide
end Hadamard668
