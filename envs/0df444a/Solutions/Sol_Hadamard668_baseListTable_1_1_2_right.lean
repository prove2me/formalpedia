-- Prove2me | solution 1 for Hadamard668.baseListTable_1_1_2_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:04:47.752984+00:00
-- url     : https://prove2.me/submissions/053c8239-8b8a-4309-8920-cea642addc77

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
    baseListTable 1 1 2 true = baseExpectedTable 1 1 2 true := by
  decide
end Hadamard668
