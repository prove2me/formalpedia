-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:41.9948+00:00
-- url     : https://prove2.me/submissions/c8ac1f55-d6ac-4560-8596-18c42f938c28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_w
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_main
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_integral_main
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_abel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (P : ℕ → Prop) (θ : ℤ) {β φ ρ Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X)
    (h : ∀ u ∈ Set.Icc Y X, |φ * (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    |φ * (cnt P X - cnt P Y) - (Emain θ β X - Emain θ β Y)| ≤
      ρ * (Emain θ β X - Emain θ β Y + 2 * (mainPsi θ β Y / Real.log Y)) := by
  have hlY := Real.log_pos hY
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have iA : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2
      (integrableOn_mul_sum_Icc (wt P) (by linarith) (contOn_w hY).integrableOn_Icc)
  have iB : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2) * mainPsi θ β t) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2 (contOn_main θ β hY).integrableOn_Icc
  have hw : ∀ t ∈ Set.Icc Y X, 0 ≤ 1 / (t * Real.log t ^ 2) := fun t ht => by
    have : 0 < t := by linarith [ht.1]
    positivity
  have u1 := intervalIntegral.integral_mono_on hYX (iA.const_mul φ) (iB.const_mul (1 + ρ)) fun t ht => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (h t ht)).2 (hw t ht)
    linarith
  have u2 := intervalIntegral.integral_mono_on hYX (iB.const_mul (1 - ρ)) (iA.const_mul φ) fun t ht => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (h t ht)).1 (hw t ht)
    linarith
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_main θ hβ hY hYX] at u1 u2
  obtain ⟨x1, x2⟩ := abs_le.1 (h X ⟨hYX, le_rfl⟩)
  obtain ⟨y1, y2⟩ := abs_le.1 (h Y ⟨le_rfl, hYX⟩)
  have x1 := mul_le_mul_of_nonneg_left x1 (inv_pos.2 hlX).le
  have x2 := mul_le_mul_of_nonneg_left x2 (inv_pos.2 hlX).le
  have y1 := mul_le_mul_of_nonneg_left y1 (inv_pos.2 hlY).le
  have y2 := mul_le_mul_of_nonneg_left y2 (inv_pos.2 hlY).le
  rw [abel P hY hYX, abs_le]
  simp only [div_eq_mul_inv] at *
  constructor <;> linarith
end GlobalTheory.Lin.PsiToPi
