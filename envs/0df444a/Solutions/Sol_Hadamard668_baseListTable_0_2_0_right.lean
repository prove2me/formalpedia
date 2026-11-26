-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:59:49.276795+00:00
-- url     : https://prove2.me/submissions/6c218279-c89a-428c-91d8-1fb2557ef19b

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
    baseListTable 0 2 0 true = baseExpectedTable 0 2 0 true := by
  decide
end Hadamard668
