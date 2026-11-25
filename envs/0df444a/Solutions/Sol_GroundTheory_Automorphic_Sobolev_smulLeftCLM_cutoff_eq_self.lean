-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_cutoff_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:22.142332+00:00
-- url     : https://prove2.me/submissions/13a25ff8-35a8-4bc3-84b6-c269b547813d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_cutoff_eq_one
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
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {R : ℝ} (u : 𝓢'(E, F')) (hu : Distribution.IsVanishingOn u (Metric.closedBall (0 : E) R)ᶜ) :
    smulLeftCLM F' (cutoff R : E → ℂ) u = u := by
  ext φ
  rw [smulLeftCLM_apply_apply]
  have h0 : u (SchwartzMap.smulLeftCLM ℂ (cutoff R : E → ℂ) φ - φ) = 0 := by
    apply hu
    have hsub : Function.support ⇑(SchwartzMap.smulLeftCLM ℂ (cutoff R : E → ℂ) φ - φ) ⊆
        (Metric.ball (0 : E) (R + 1))ᶜ := by
      intro x hx
      by_contra hb
      apply hx
      simp only [Set.mem_compl_iff, not_not] at hb
      rw [sub_apply, SchwartzMap.smulLeftCLM_apply_apply
        (cutoff R).hasTemperateGrowth, cutoff_eq_one hb, one_smul, sub_self]
    refine (closure_minimal hsub Metric.isOpen_ball.isClosed_compl).trans ?_
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_ball, Metric.mem_closedBall, not_lt, not_le] at hx ⊢
    linarith
  rw [map_sub, sub_eq_zero] at h0
  exact h0
end GroundTheory.Automorphic.Sobolev
