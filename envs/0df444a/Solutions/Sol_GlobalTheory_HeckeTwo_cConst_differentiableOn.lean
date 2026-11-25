-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.cConst_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:30.024776+00:00
-- url     : https://prove2.me/submissions/db0f3fe7-d3bd-4fa0-ae07-f43b37881a65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_cConst_eq
import Theorems.Thm_GlobalTheory_HeckeTwoC_bound_G
import Theorems.Thm_P2M_GlobalTheory_HeckeTwoC_bound_G__e6ab55a3392d
import Theorems.Thm_GlobalTheory_HeckeTwoC_integrable_expL
import Theorems.Thm_GlobalTheory_HeckeTwoC_hasDerivAt_G
import Theorems.Thm_GlobalTheory_HeckeTwoC_continuous_G
import Theorems.Thm_P2M_GlobalTheory_HeckeTwoC_continuous_G__26b518ce0d24

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
open MeasureTheory GlobalTheory.HeckeTwoC
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : DifferentiableOn ℂ cConst halfPlane := by
  rw [cConst_eq]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := (abs_lt.1 (lt_of_le_of_lt h1 h2)).1
    simp only [sub_re] at h3
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := G) (F' := G')
    (x₀ := σ₀) (bound := fun t => 2 / ε * Real.exp (-(1 + ε) * lg t))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_G σ).aestronglyMeasurable)
    ((integrable_expL hε).mono' (continuous_G σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_G hε (hball σ₀ (Metric.mem_ball_self hε)) t))
    (continuous_G' σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_G' hε (hball σ hσ) t)
    ((integrable_expL hε).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_G σ t)
  exact key.2.differentiableAt.differentiableWithinAt
end GlobalTheory.HeckeTwo
