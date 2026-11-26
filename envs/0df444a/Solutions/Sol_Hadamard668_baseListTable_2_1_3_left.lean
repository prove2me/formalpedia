-- Prove2me | solution 1 for Hadamard668.baseListTable_2_1_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:10:06.289205+00:00
-- url     : https://prove2.me/submissions/b9726cd0-01f6-46ec-a485-f64053212fc5

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
    baseListTable 2 1 3 false = baseExpectedTable 2 1 3 false := by
  decide
end Hadamard668
