-- Prove2me | solution 1 for Hadamard668.baseListTable_1_1_2_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:04:29.540446+00:00
-- url     : https://prove2.me/submissions/81271f50-14d7-4449-8458-fc5f224cbdf9

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
    baseListTable 1 1 2 false = baseExpectedTable 1 1 2 false := by
  decide
end Hadamard668
