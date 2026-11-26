-- Prove2me | solution 1 for Hadamard668.baseListTable_3_2_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:15:53.436438+00:00
-- url     : https://prove2.me/submissions/1ac6eaa2-c722-4a18-bb58-eb1c7b054b2b

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
    baseListTable 3 2 2 false = baseExpectedTable 3 2 2 false := by
  decide
end Hadamard668
