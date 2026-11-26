-- Prove2me | solution 1 for Hadamard668.baseListTable_2_3_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:12:44.451684+00:00
-- url     : https://prove2.me/submissions/4d01df86-449a-42de-a1d0-d9f682158b69

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
    baseListTable 2 3 3 false = baseExpectedTable 2 3 3 false := by
  decide
end Hadamard668
