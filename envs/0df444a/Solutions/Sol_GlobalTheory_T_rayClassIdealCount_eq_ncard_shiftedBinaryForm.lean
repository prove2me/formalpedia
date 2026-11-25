-- Prove2me | solution 1 for GlobalTheory.T.rayClassIdealCount_eq_ncard_shiftedBinaryForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:51.5336+00:00
-- url     : https://prove2.me/submissions/d5f4f2af-8ab3-49ce-842b-19a6831fdcf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
import Theorems.Thm_GlobalTheory_Hk_RayForm_aRay_eq_ncard_qForm


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
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, ∃ α γ l θ₁ θ₂ : ℝ, 1 ≤ α ∧ 1 ≤ γ ∧ α * γ = d * (M : ℝ) ^ 4 / 4 ∧ (∀ v : ℤ × ℤ, ∃ n : ℕ, 1 ≤ n ∧ qForm α γ l θ₁ θ₂ v = n) ∧ ∀ n : ℕ, aRay D g n = (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n}.ncard : ℕ) : ℝ) := by
  first | exact @GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm | exact GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm | (intros; apply GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm <;> assumption)
end _root_.GlobalTheory.T
