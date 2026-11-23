-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:15:56.115595+00:00
-- url     : https://prove2.me/submissions/46e5f94f-7311-4aef-9a5a-dfedb2f1dacf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Published.Metaplectic
theorem _root_.solution : Function.HasTemperateGrowth (eChar : ℝ → ℂ) := by
  have hf : (eChar : ℝ → ℂ) = fun x : ℝ => cexp (2 * π * x * I) := funext eChar_apply
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (2 * π * y * I : ℂ)) (2 * π * I) x := by
    intro x
    have h := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * π : ℂ)).mul_const I
    simpa using h
  have hd : ∀ c : ℂ, deriv (fun x : ℝ => c * cexp (2 * π * x * I)) =
      fun x : ℝ => c * (2 * π * I) * cexp (2 * π * x * I) := by
    intro c
    funext x
    rw [((hlin x).cexp.const_mul c).deriv]
    ring
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => cexp (2 * π * x * I)) =
      fun x : ℝ => (2 * π * I) ^ n * cexp (2 * π * x * I) := by
    intro n
    induction n with
    | zero => funext x; simp
    | succ n ih => rw [iteratedDeriv_succ, ih, hd, pow_succ]
  have hnorm : ∀ x : ℝ, ‖cexp (2 * π * x * I)‖ = 1 := by
    intro x
    rw [show (2 * π * x * I : ℂ) = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hf]
  refine ⟨?_, fun n => ⟨0, (2 * π) ^ n, fun x => ?_⟩⟩
  · exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit n]
    simp only [norm_mul, norm_pow, hnorm, mul_one, pow_zero]
    simp [abs_of_pos Real.pi_pos]
end GlobalTheory.Published.Metaplectic
