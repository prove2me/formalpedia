-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.summable_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:14.370477+00:00
-- url     : https://prove2.me/submissions/59f9b2ac-e6d6-4926-bfd5-9b292bbd77e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
import Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_exists_coercive
import Theorems.Thm_GlobalTheory_GaussCoset_summable_gaussian_coset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries
namespace GlobalTheory.HeisenbergGaussianSeries
theorem _root_.solution {G V : Type} [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (p : G →+ V) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ U₀ : AddSubgroup G) (χ : G → ℂ) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v))
    (hinj : ∀ g ∈ Γ, p g = 0 → g = 0)
    (hfin : ∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite)
    (hχ0 : ∀ x, x ∉ U₀ → χ x = 0) (hχ1 : ∀ x, ‖χ x‖ ≤ 1)
    (b : Γ → ℂ) (hb : ∀ g, ‖b g‖ = 1) (w : G) (y : V) (M : V →L[ℝ] V →L[ℝ] ℂ) (R : ℝ) :
    Summable fun g : Γ => ‖b g * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))‖ *
        Real.exp (R * ‖M (p g + y)‖) := by
  obtain ⟨c, hc, hq⟩ := exists_coercive om J hpos
  have hs := GlobalTheory.GaussCoset.summable_gaussian_coset G V p Γ U₀ hinj hfin (Real.pi / 2 * c) (by positivity) (|R| * ‖M‖) w y
  refine Summable.of_nonneg_of_le (fun g => by positivity) (fun g => ?_) hs
  by_cases hg : (g : G) + w ∈ U₀
  · rw [Set.indicator_of_mem (by exact hg), norm_mul, norm_mul, hb, one_mul, Complex.norm_exp,
      Real.exp_add]
    have h1 : (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ)).re
        = -(Real.pi / 2) * om (p g + y) (J (p g + y)) := by
      have : (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))
        = ((-(Real.pi / 2) * om (p g + y) (J (p g + y)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [h1]
    have h2 : -(Real.pi / 2) * om (p g + y) (J (p g + y))
        ≤ -(Real.pi / 2 * c) * ‖p g + y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hq (p g + y)) (show 0 ≤ Real.pi / 2 by positivity)
      linarith
    have h3 : R * ‖M (p g + y)‖ ≤ |R| * ‖M‖ * ‖p g + y‖ := by
      rw [mul_assoc]
      exact mul_le_mul (le_abs_self R) (M.le_opNorm _) (norm_nonneg _) (abs_nonneg _)
    refine mul_le_mul ?_ (Real.exp_le_exp.mpr h3) (by positivity) (by positivity)
    exact (mul_le_of_le_one_left (by positivity) (hχ1 _)).trans (Real.exp_le_exp.mpr h2)
  · rw [Set.indicator_of_notMem (by exact hg), hχ0 _ hg]
    simp
end GlobalTheory.HeisenbergGaussianSeries
