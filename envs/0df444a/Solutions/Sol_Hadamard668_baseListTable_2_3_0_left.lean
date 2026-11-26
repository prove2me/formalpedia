-- Prove2me | solution 1 for Hadamard668.baseListTable_2_3_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:11:41.787904+00:00
-- url     : https://prove2.me/submissions/ce5a5db2-ca90-4be2-afaf-9f0ead65a216

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
    baseListTable 2 3 0 false = baseExpectedTable 2 3 0 false := by
  decide
end Hadamard668
