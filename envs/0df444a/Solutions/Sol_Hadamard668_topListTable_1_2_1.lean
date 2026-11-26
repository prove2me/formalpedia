-- Prove2me | solution 1 for Hadamard668.topListTable_1_2_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:21:16.661082+00:00
-- url     : https://prove2.me/submissions/696d0b54-05b9-4521-aeae-3f6669bf5313

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
    topListTable 1 2 1 = topExpectedTable 1 2 1 := by
  decide
end Hadamard668
