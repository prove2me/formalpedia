-- Prove2me | solution 1 for Hadamard668.baseListTable_0_2_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:00:58.167649+00:00
-- url     : https://prove2.me/submissions/11120b20-5b2c-41e5-ab25-0253ccf5dda8

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
    baseListTable 0 2 3 false = baseExpectedTable 0 2 3 false := by
  decide
end Hadamard668
