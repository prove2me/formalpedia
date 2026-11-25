-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.hTransAB_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:03.996297+00:00
-- url     : https://prove2.me/submissions/860bdd47-e8ed-4fb5-8bfb-4a01cfa277cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_hTransAB_eq
import Theorems.Thm_GlobalTheory_HeckeTwoAB_bound_F
import Theorems.Thm_P2M_GlobalTheory_HeckeTwoAB_bound_F__ff0e78d4a637
import Theorems.Thm_GlobalTheory_HeckeTwoAB_integrable_bound
import Theorems.Thm_GlobalTheory_HeckeTwoAB_hasDerivAt_F
import Theorems.Thm_GlobalTheory_HeckeTwoAB_continuous_F
import Theorems.Thm_P2M_GlobalTheory_HeckeTwoAB_continuous_F__ed6efc273c97

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
open GlobalTheory GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoC GlobalTheory.HeckeTwoAB
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 →
    DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  intro a b ν y hab hy
  rw [hTransAB_eq a b ν hy]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hab' : (2 : ℝ) ≤ (a + b : ℝ) := by exact_mod_cast hab
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re ∧ σ.re ≤ σ₀.re + ε := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := abs_lt.1 (lt_of_le_of_lt h1 h2)
    simp only [sub_re] at h3
    constructor <;> linarith [h3.1, h3.2]
  set M := (a + b : ℝ) + 2 * (σ₀.re + ε) with hM_def
  have hc : ∀ σ ∈ Metric.ball σ₀ ε, 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re := by
    intro σ hσ; have := (hball σ hσ).1; linarith
  have hM : ∀ σ ∈ Metric.ball σ₀ ε, (a + b : ℝ) + 2 * σ.re ≤ M := by
    intro σ hσ; have := (hball σ hσ).2; rw [hM_def]; linarith
  have h0 := Metric.mem_ball_self hε (x := σ₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F a b ν y)
    (F' := F' a b ν y) (x₀ := σ₀)
    (bound := fun t => 2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) *
      Real.exp (-(1 + ε) * lg (t / y)))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_F a b ν hy σ).aestronglyMeasurable)
    (((integrable_bound hε hy).const_mul (Real.exp (M * |Real.log (abs y)|))).mono'
      (continuous_F a b ν hy σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_F hε a b ν hy (hc σ₀ h0) (hM σ₀ h0) t))
    (continuous_F' a b ν hy σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_F' hε a b ν hy (hc σ hσ) (hM σ hσ) t)
    ((integrable_bound hε hy).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_F a b ν y σ t)
  exact key.2.differentiableAt.differentiableWithinAt
end GlobalTheory.HeckeTwo
