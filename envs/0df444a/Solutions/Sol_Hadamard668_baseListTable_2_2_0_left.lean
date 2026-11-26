-- Prove2me | solution 1 for Hadamard668.baseListTable_2_2_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:10:13.244199+00:00
-- url     : https://prove2.me/submissions/03a583a4-b2ae-426e-b800-c0a6f9b1c0d0

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
    baseListTable 2 2 0 false = baseExpectedTable 2 2 0 false := by
  decide
end Hadamard668
