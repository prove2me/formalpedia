-- Prove2me | solution 1 for Hadamard668.baseListTable_3_1_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:14:11.863746+00:00
-- url     : https://prove2.me/submissions/e4e3d64d-d82b-4ab3-acfe-f2d38b312438

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
    baseListTable 3 1 0 false = baseExpectedTable 3 1 0 false := by
  decide
end Hadamard668
