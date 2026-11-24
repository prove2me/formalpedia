-- Prove2me | solution 1 for GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:24:45.684797+00:00
-- url     : https://prove2.me/submissions/4f7a5aef-b3f3-498c-8779-460a3a099236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_pi_prod
import Theorems.Thm_GlobalTheory_SW_SiegelSum_exists_mul_dotProduct_le
import Theorems.Thm_GlobalTheory_SW_SiegelSum_exists_int_of_intM
import Theorems.Thm_GlobalTheory_SW_SiegelSum_exists_bound
import Theorems.Thm_GlobalTheory_SW_SiegelSum_sum_le_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum
namespace GlobalTheory.SW.SiegelSum
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ), IsSB φ → ∀ τ ∈ Siegel ι, ∀ ζ : κ → ι → ℂ, Summable fun x : Matrix κ ι ℚ => ‖φ x * cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ := by
  intro κ ι _ _ _ φ ⟨R, hR, h⟩ τ hτ ζ
  obtain ⟨M, hM⟩ := exists_bound hR h
  obtain ⟨c, hc0, hc⟩ := exists_mul_dotProduct_le hτ.2
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hS : ∀ k i, |(ζ k i).im| ≤ ‖ζ‖ := fun k i =>
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (ζ k) i).trans (norm_le_pi_norm ζ k))
  let e : (κ → ι → ℤ) → Matrix κ ι ℚ := fun n => Matrix.of fun k i => (n k i : ℚ) / R
  have he : Function.Injective e := by
    intro m n hmn
    funext k i
    have h1 : (m k i : ℚ) / R = (n k i : ℚ) / R := congrFun (congrFun hmn k) i
    have : (R : ℚ) ≠ 0 := by positivity
    exact_mod_cast (div_left_inj' this).1 h1
  refine (he.summable_iff fun x hx => ?_).1 ?_
  · have : φ x = 0 := by
      by_contra h0
      obtain ⟨n, hn⟩ := exists_int_of_intM hR (h.1 x h0)
      exact hx ⟨n, hn.symm⟩
    simp [this]
  let f : ℤ → ℝ := fun n => Real.exp (-π * (c / R ^ 2 * n ^ 2 - 2 * (‖ζ‖ / R) * |n|))
  have hf : Summable f := by
    simpa [f] using summable_pow_mul_jacobiTheta₂_term_bound (‖ζ‖ / R)
      (T := c / R ^ 2) (by positivity) 0
  have hs : Summable fun n : κ → ι → ℤ => ∏ k, ∏ i, f (n k i) :=
    summable_pi_prod (fun (_ : κ) (m : ι → ℤ) => ∏ i, f (m i))
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
      fun _ => summable_pi_prod (fun _ => f) (fun _ _ => (Real.exp_pos _).le) fun _ => hf
  refine (hs.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [Function.comp_apply, norm_mul]
  refine mul_le_mul (hM _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
  simp only [f, ← Real.exp_sum, Complex.norm_exp, Real.exp_le_exp, ← Finset.mul_sum]
  have h1 : ∀ z : ℂ, (π * I * z).re = -π * z.im := fun z => by simp
  rw [h1, Complex.im_sum]
  refine mul_le_mul_of_nonpos_left (Finset.sum_le_sum fun k _ => ?_) (by linarith [Real.pi_pos])
  refine le_trans (le_of_eq ?_) (sum_le_im hc (ζ k) (hS k) (e n k))
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [e, of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div, Nat.abs_cast,
    Int.cast_abs]
  field_simp
end GlobalTheory.SW.SiegelSum
