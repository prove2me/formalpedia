-- Prove2me | solution 1 for Hadamard668.baseListTable_0_3_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:01:39.174682+00:00
-- url     : https://prove2.me/submissions/ecc45ddf-b755-41e2-9aa4-ca07ab8f5928

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
    baseListTable 0 3 0 false = baseExpectedTable 0 3 0 false := by
  decide
end Hadamard668
