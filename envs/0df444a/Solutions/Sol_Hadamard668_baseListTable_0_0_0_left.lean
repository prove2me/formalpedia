-- Prove2me | solution 1 for Hadamard668.baseListTable_0_0_0_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:58:00.786715+00:00
-- url     : https://prove2.me/submissions/f00c60d9-3105-4e62-95aa-822fa1e887c9

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
    baseListTable 0 0 0 false = baseExpectedTable 0 0 0 false := by
  decide
end Hadamard668
