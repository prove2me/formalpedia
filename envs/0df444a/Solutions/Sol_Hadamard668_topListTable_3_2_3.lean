-- Prove2me | solution 1 for Hadamard668.topListTable_3_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:26:09.529322+00:00
-- url     : https://prove2.me/submissions/3ce8503b-a8eb-441f-ad34-f0d4d6817d60

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
    topListTable 3 2 3 = topExpectedTable 3 2 3 := by
  decide
end Hadamard668
