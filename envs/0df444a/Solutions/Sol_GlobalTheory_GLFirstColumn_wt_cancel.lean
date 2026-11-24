-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.wt_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:13.01881+00:00
-- url     : https://prove2.me/submissions/ce871fbf-3b07-4348-b63d-101dacd88b3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {m : ℕ} (a : Fin m → Fin m → ℂ) (ha : (Matrix.of a).det ≠ 0) :
    ENNReal.ofReal ((‖(Matrix.of a).det‖ ^ 2) ^ m) * wt a = 1 := by
  have : ‖(Matrix.of a).det‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ha)
  unfold wt
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel₀ this, one_pow,
    ENNReal.ofReal_one]
end GlobalTheory.GLFirstColumn
