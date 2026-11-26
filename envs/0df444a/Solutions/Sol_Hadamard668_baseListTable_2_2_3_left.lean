-- Prove2me | solution 1 for Hadamard668.baseListTable_2_2_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:11:14.763966+00:00
-- url     : https://prove2.me/submissions/82188e62-0472-4fc0-a43d-f6d6d625e6be

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
    baseListTable 2 2 3 false = baseExpectedTable 2 2 3 false := by
  decide
end Hadamard668
