-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.Red.sm_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:49.451939+00:00
-- url     : https://prove2.me/submissions/fb4a3578-4dcc-423c-8d1f-56f9ced4f3c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.UnitDiscAlg.Red
theorem _root_.solution {x : Matrix (Fin n) (Fin n) E} (hx : Sm x) : Sm (-x) := by
  intro i j; rw [Matrix.neg_apply, norm_neg]; exact hx i j
end GlobalTheory.UnitDiscAlg.Red
