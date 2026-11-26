-- Prove2me | solution 1 for Hadamard668.topListTable_3_3_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:26:20.732724+00:00
-- url     : https://prove2.me/submissions/618b3fac-3524-4ec3-84be-c64816781cc3

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
    topListTable 3 3 0 = topExpectedTable 3 3 0 := by
  decide
end Hadamard668
