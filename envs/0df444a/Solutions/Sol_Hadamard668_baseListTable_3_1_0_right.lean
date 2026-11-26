-- Prove2me | solution 1 for Hadamard668.baseListTable_3_1_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:14:12.456157+00:00
-- url     : https://prove2.me/submissions/3cb63ad2-221c-4730-8d6b-497114466241

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
    baseListTable 3 1 0 true = baseExpectedTable 3 1 0 true := by
  decide
end Hadamard668
