-- Prove2me | solution 1 for Hadamard668.baseListTable_1_2_3_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:05:45.398504+00:00
-- url     : https://prove2.me/submissions/94dd4158-86b6-4abc-bad9-25a6726de183

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
    baseListTable 1 2 3 false = baseExpectedTable 1 2 3 false := by
  decide
end Hadamard668
