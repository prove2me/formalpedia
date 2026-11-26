-- Prove2me | solution 1 for Hadamard668.baseListTable_0_0_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:58:19.482192+00:00
-- url     : https://prove2.me/submissions/41335f0f-50f7-4ba6-9057-9bb0c2703577

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
    baseListTable 0 0 3 false = baseExpectedTable 0 0 3 false := by
  decide
end Hadamard668
