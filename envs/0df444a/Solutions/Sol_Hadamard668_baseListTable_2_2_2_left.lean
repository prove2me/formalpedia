-- Prove2me | solution 1 for Hadamard668.baseListTable_2_2_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:11:02.829257+00:00
-- url     : https://prove2.me/submissions/ea27a163-6cb1-4fc6-83c2-2688d6df5d59

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
    baseListTable 2 2 2 false = baseExpectedTable 2 2 2 false := by
  decide
end Hadamard668
