-- Prove2me | solution 1 for Hadamard668.baseListTable_2_3_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:12:27.500141+00:00
-- url     : https://prove2.me/submissions/8da6ad6a-a605-4571-9926-14c9c078af73

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
    baseListTable 2 3 2 false = baseExpectedTable 2 3 2 false := by
  decide
end Hadamard668
