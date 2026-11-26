-- Prove2me | solution 1 for Hadamard668.topListTable_1_1_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:20:21.811229+00:00
-- url     : https://prove2.me/submissions/b082adc4-924f-41e1-9ea5-404959b596fc

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
    topListTable 1 1 1 = topExpectedTable 1 1 1 := by
  decide
end Hadamard668
