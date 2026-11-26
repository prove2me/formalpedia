-- Prove2me | solution 1 for Hadamard668.baseListTable_3_2_0_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:15:32.086602+00:00
-- url     : https://prove2.me/submissions/b64f4473-98c7-48aa-b945-fa69dff4669a

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
    baseListTable 3 2 0 true = baseExpectedTable 3 2 0 true := by
  decide
end Hadamard668
