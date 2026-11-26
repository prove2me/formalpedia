-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:12:48.325684+00:00
-- url     : https://prove2.me/submissions/9993d742-c44a-438a-829a-cc536d0bc5b0

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
    baseListTable 3 0 0 false = baseExpectedTable 3 0 0 false := by
  decide
end Hadamard668
