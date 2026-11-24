-- Prove2me | solution 1 for GlobalTheory.TermEst.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:17.796822+00:00
-- url     : https://prove2.me/submissions/f2b7061e-f322-4b9f-a945-201753c08c3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianConvolutionSeriesCoefficientDescFactoria
import Theorems.Thm_GlobalTheory_TermEst_pointwise
import Theorems.Thm_GlobalTheory_TermEst_norm_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TermEst
namespace GlobalTheory.TermEst
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c θ α : ℝ), 0 < c → 1 ≤ θ → 0 < α → c * θ ^ 2 ≤ α * (b + c) →
    ∀ (h : SchwartzMap E ℂ) (j i : ℕ) (y : E),
    (2 * c) ^ j / (j.factorial : ℝ) * (j.descFactorial i : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) *
      ‖y‖ ^ (j - i) ≤ θ⁻¹ ^ (j - i) * Real.exp (c * α * ‖y‖ ^ 2) * ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ := by
  intro E _ _ _ _ _ b c θ α hc hθ hα hk h j i y
  rcases lt_or_ge j i with hji | hij
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hji, Nat.cast_zero, mul_zero, zero_mul, zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg fun a => by positivity)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.add_sub_cancel_left]
    have hK : (2 * c) ^ (i + m) / ((i + m).factorial : ℝ) * ((i + m).descFactorial i : ℝ) =
        (2 * c) ^ (i + m) / (m.factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (Nat.le_add_right i m)
      rw [Nat.add_sub_cancel_left] at this
      have h1 : ((i + m).factorial : ℝ) = (m.factorial : ℝ) * ((i + m).descFactorial i : ℝ) := by
        exact_mod_cast this.symm
      have h2 : (0 : ℝ) < m.factorial := by positivity
      have h3 : (0 : ℝ) < ((i + m).descFactorial i : ℝ) := by
        have : (0:ℝ) < ((i + m).factorial : ℝ) := by positivity
        rw [h1] at this
        exact pos_of_mul_pos_right this h2.le
      rw [h1]; field_simp
    rw [hK]
    have hint : Integrable (fun a : E => (2 * c * ‖a‖) ^ i * ‖h a‖) := by
      have := (h.integrable_pow_mul volume i).const_mul ((2 * c) ^ i)
      refine this.congr (Eventually.of_forall fun a => ?_)
      simp only [mul_pow]; ring
    calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ (i + m)) * ‖y‖ ^ m
        = ∫ a, (2 * c) ^ (i + m) / (m.factorial : ℝ) * ‖y‖ ^ m *
            (Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ * ‖a‖ ^ (i + m)) := by
          rw [integral_const_mul]; simp only [norm_wt]; ring
      _ ≤ ∫ a, θ⁻¹ ^ m * Real.exp (c * α * ‖y‖ ^ 2) * ((2 * c * ‖a‖) ^ i * ‖h a‖) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun a => by positivity)
            (hint.const_mul _) (Eventually.of_forall fun a => ?_)
          exact pointwise b c θ α ‖a‖ ‖y‖ ‖h a‖ hc hθ hα hk (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) i m
      _ = _ := integral_const_mul _ _
end GlobalTheory.TermEst
