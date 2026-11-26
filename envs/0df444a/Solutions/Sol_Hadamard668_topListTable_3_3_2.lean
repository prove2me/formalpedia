-- Prove2me | solution 1 for Hadamard668.topListTable_3_3_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:27:03.699151+00:00
-- url     : https://prove2.me/submissions/5792c337-2329-4178-b868-e34318ff1e4f

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
    topListTable 3 3 2 = topExpectedTable 3 3 2 := by
  decide
end Hadamard668
