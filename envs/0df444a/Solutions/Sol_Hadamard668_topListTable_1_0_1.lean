-- Prove2me | solution 1 for Hadamard668.topListTable_1_0_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:20:02.379872+00:00
-- url     : https://prove2.me/submissions/05bbdad2-b0c6-49ec-a580-66968d3cc08c

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
    topListTable 1 0 1 = topExpectedTable 1 0 1 := by
  decide
end Hadamard668
