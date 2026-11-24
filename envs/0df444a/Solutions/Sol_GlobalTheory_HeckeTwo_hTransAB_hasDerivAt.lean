-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.hTransAB_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:53.039524+00:00
-- url     : https://prove2.me/submissions/894cbfd5-1a90-4617-ac46-27c64bb5ca0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_hTransAB_eq
import Theorems.Thm_GlobalTheory_HeckeTwoDY_hasDerivAt_igE
import Theorems.Thm_GlobalTheory_HeckeTwoDY_integrable_bd
import Theorems.Thm_GlobalTheory_HeckeTwoDY_continuous_igE
import Theorems.Thm_GlobalTheory_HeckeTwoDY_integrable_igE
import Theorems.Thm_GlobalTheory_HeckeTwoDY_norm_igE_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoDY
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y := by
  intro a b σ ν y hab hσ hy
  have hre : -1 / 2 < σ.re := hσ
  have hab' : (2 : ℝ) ≤ a + b := by exact_mod_cast hab
  have hypos : 0 < |y| := abs_pos.2 hy
  have hε : 0 < |y| / 2 := by linarith
  have hball : ∀ y' ∈ Metric.ball y (|y| / 2), |y' - y| < |y| / 2 := fun y' h => by
    simpa [Metric.mem_ball, Real.dist_eq] using h
  have hne : ∀ y' ∈ Metric.ball y (|y| / 2), y' ≠ 0 := fun y' h => by
    have h0 := hball y' h
    intro e; rw [e, zero_sub, abs_neg] at h0; linarith
  have hy2 : y / 2 ≠ 0 := div_ne_zero hy two_ne_zero
  have hk : 0 ≤ ((a + 1 : ℕ) : ℝ) + b + 2 * σ.re := by push_cast; linarith
  have hk' : 0 ≤ (a : ℝ) + ((b + 1 : ℕ) : ℝ) + 2 * σ.re := by push_cast; linarith
  have e1 : ((a + 1 : ℕ) : ℝ) + b + 2 * σ.re = (a : ℝ) + b + 2 * σ.re + 1 := by push_cast; ring
  have e2 : (a : ℝ) + ((b + 1 : ℕ) : ℝ) + 2 * σ.re = (a : ℝ) + b + 2 * σ.re + 1 := by push_cast; ring
  set k := (a : ℝ) + b + 2 * σ.re with hk_def
  have hint1 := integrable_igE ν (a := a + 1) (b := b) (by omega) hre hy
  have hint2 := integrable_igE ν (a := a) (b := b + 1) (by omega) hre hy
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y' t => igE a b σ ν y' t)
    (F' := fun y' t => I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y' t + I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y' t)
    (x₀ := y)
    (bound := fun t => (‖-(a : ℂ) - σ‖ + ‖(b : ℂ) + σ‖) * Real.exp (-((k + 1) / 2) * Real.log (t ^ 2 + (y / 2) ^ 2)))
    (Metric.ball_mem_nhds y hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y hε) fun y' h => (continuous_igE a b σ ν (hne y' h)).aestronglyMeasurable)
    (integrable_igE ν hab hre hy)
    (((continuous_igE (a + 1) b σ ν hy).const_mul _).add ((continuous_igE a (b + 1) σ ν hy).const_mul _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t y' hy' => by
      have b1 := norm_igE_le (ν := ν) hk hy (hball y' hy') t
      have b2 := norm_igE_le (ν := ν) hk' hy (hball y' hy') t
      rw [e1] at b1; rw [e2] at b2
      calc _ ≤ ‖I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y' t‖ + ‖I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y' t‖ := norm_add_le _ _
        _ = ‖-(a : ℂ) - σ‖ * ‖igE (a + 1) b σ ν y' t‖ + ‖(b : ℂ) + σ‖ * ‖igE a (b + 1) σ ν y' t‖ := by
          simp only [norm_mul, Complex.norm_I, one_mul]
        _ ≤ _ := by
          rw [add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left b1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left b2 (norm_nonneg _)))
    ((integrable_bd (k := k + 1) (by linarith) hy2).const_mul _)
    (Filter.Eventually.of_forall fun t y' hy' => hasDerivAt_igE a b σ ν t (hne y' hy'))
  have hfun : (fun y' : ℝ => hTransAB a b σ ν y') =ᶠ[nhds y] fun y' => ∫ t, igE a b σ ν y' t :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds y hε) fun y' h => hTransAB_eq (hne y' h)
  refine (key.2.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul,
    hTransAB_eq hy, hTransAB_eq hy]
end GlobalTheory.HeckeTwo
