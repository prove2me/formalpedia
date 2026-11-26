-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_3_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:14:09.560281+00:00
-- url     : https://prove2.me/submissions/5c61408f-5ae0-4325-a1f2-5342a5ea3dfa

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
    baseListTable 3 0 3 true = baseExpectedTable 3 0 3 true := by
  decide
end Hadamard668
