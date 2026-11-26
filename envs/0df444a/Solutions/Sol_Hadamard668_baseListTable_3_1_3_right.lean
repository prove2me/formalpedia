-- Prove2me | solution 1 for Hadamard668.baseListTable_3_1_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:15:03.807789+00:00
-- url     : https://prove2.me/submissions/8bef0724-10fb-4392-971b-35089abf238d

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
    baseListTable 3 1 3 true = baseExpectedTable 3 1 3 true := by
  decide
end Hadamard668
