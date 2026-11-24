-- Prove2me | solution 1 for GlobalTheory.T.abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:45.775197+00:00
-- url     : https://prove2.me/submissions/bbcd0e36-4e06-4d00-885e-266e3b1d809f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Theorems.Thm_GlobalTheory_Hk_qForm_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ α γ l θ₁ θ₂ x : ℝ, 1 ≤ α → 1 ≤ γ → 1 ≤ x → {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.Finite ∧ |(({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.ncard : ℕ) : ℝ) - Real.pi / Real.sqrt (α * γ) * x| ≤ 10 * Real.sqrt x := by
  first | exact @GlobalTheory.Hk.qForm_count | exact GlobalTheory.Hk.qForm_count | (intros; apply GlobalTheory.Hk.qForm_count <;> assumption)
end _root_.GlobalTheory.T
