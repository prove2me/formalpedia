-- Prove2me | solution 1 for HlawkaCodex84SOSCache.gram_rows1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:28:45.986987+00:00
-- url     : https://prove2.me/submissions/a566c7b9-91fc-472d-ae8f-182a013012c9

import Definitions.Def_HlawkaCodex84_SOSCertificateData
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open HlawkaCodex84SOSCache
theorem solution : ∀ (i : Fin 10) (j : Fin 30), gram ⟨i.val + 10, by omega⟩ j = (gramLower * Matrix.diagonal gramPivots * gramLower.transpose) ⟨i.val + 10, by omega⟩ j := by decide +kernel
#print axioms solution
