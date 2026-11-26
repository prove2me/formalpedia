-- Prove2me | solution 1 for Hadamard668.baseListTable_0_3_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:01:53.641465+00:00
-- url     : https://prove2.me/submissions/3e778ea1-34c7-482f-8962-91d3decfb018

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
    baseListTable 0 3 2 false = baseExpectedTable 0 3 2 false := by
  decide
end Hadamard668
