-- Prove2me | solution 1 for Hadamard668.baseListTable_1_2_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:05:24.215706+00:00
-- url     : https://prove2.me/submissions/a916c304-f12b-4702-a43b-a88e387cb88e

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
    baseListTable 1 2 0 false = baseExpectedTable 1 2 0 false := by
  decide
end Hadamard668
