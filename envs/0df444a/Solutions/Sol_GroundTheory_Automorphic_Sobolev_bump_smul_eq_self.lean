-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.bump_smul_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:14.142016+00:00
-- url     : https://prove2.me/submissions/41c8e913-152c-442d-a9f6-24b2e96bdbec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_eq_one
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_eq_self
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (x₀ : E) {r ρ : ℝ} (hr : 0 < r) (hρ : ρ < r) {z : 𝓢'(E, ℂ)}
    (hz : Distribution.IsVanishingOn z (Metric.closedBall x₀ ρ)ᶜ) :
    smulLeftCLM ℂ (bump x₀ hr : E → ℂ) z = z := by
  refine smulLeftCLM_eq_self (bump x₀ hr).hasTemperateGrowth Metric.isOpen_ball
    (fun x hx ↦ bump_eq_one x₀ hr (Metric.ball_subset_closedBall hx)) ?_ hz
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, Metric.mem_closedBall, not_le] at hx ⊢
  linarith
end GroundTheory.Automorphic.Sobolev
