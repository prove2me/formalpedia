-- Prove2me | solution 1 for Hadamard668.baseListTable_2_3_1_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:11:53.553796+00:00
-- url     : https://prove2.me/submissions/d574f7a8-3c77-4d28-8344-86220f782ea4

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
    baseListTable 2 3 1 false = baseExpectedTable 2 3 1 false := by
  decide
end Hadamard668
