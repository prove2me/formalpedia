-- Prove2me | solution 1 for Hadamard668.baseListTable_3_0_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:13:53.314658+00:00
-- url     : https://prove2.me/submissions/32afc71e-af71-4ba4-af76-02136535ad3d

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
    baseListTable 3 0 3 false = baseExpectedTable 3 0 3 false := by
  decide
end Hadamard668
