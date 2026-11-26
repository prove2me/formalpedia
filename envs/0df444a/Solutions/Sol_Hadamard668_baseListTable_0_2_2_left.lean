-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:32.10835+00:00
-- url     : https://prove2.me/submissions/8ee86290-75dd-44bb-b1cf-00e1bfdf04e1

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
    baseListTable 0 2 2 false = baseExpectedTable 0 2 2 false := by
  decide
end Hadamard668
