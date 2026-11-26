-- Prove2me | solution 1 for Hadamard668.baseListTable_3_3_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:16:31.54431+00:00
-- url     : https://prove2.me/submissions/c2a6b679-9fa6-4c68-8546-92611118a33c

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
    baseListTable 3 3 0 false = baseExpectedTable 3 3 0 false := by
  decide
end Hadamard668
