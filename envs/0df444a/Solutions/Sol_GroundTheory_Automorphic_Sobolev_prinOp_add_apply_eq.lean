-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.prinOp_add_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:15.616799+00:00
-- url     : https://prove2.me/submissions/b897a803-57ba-49a4-9c0f-d75e5a064d1c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_smul_eq_self
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_schwartz_mul
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_schwartz_sub_smul
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_iteratedLineDeriv
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_smulLeft
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
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (hNl : IsLocal N) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ < δ) {u : 𝓢'(E, ℂ)}
    (hu : Distribution.IsVanishingOn u (Metric.closedBall x₀ ρ)ᶜ) :
    (prinOp a w + N) u = P0 a w x₀ u + locM a w N x₀ hδ u := by
  have hU : IsOpen (Metric.closedBall x₀ ρ)ᶜ := Metric.isClosed_closedBall.isOpen_compl
  have hv : ∀ i, Distribution.IsVanishingOn (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) u)
      (Metric.closedBall x₀ ρ)ᶜ := fun i ↦ isLocal_iteratedLineDeriv (w i) _ hU u hu
  simp only [iteratedLineDerivOpCLM_apply] at hv
  simp only [add_apply, locM, P0, prinOp, constOp, sum_apply,
    ContinuousLinearMap.comp_apply, smul_apply, iteratedLineDerivOpCLM_apply]
  rw [bump_smul_eq_self x₀ hδ hρ (hNl _ hU u hu), ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [locCoeff, smulLeftCLM_schwartz_sub_smul, smulLeftCLM_schwartz_mul,
    bump_smul_eq_self x₀ hδ hρ (isLocal_smulLeft (a i).hasTemperateGrowth _ hU _ (hv i)),
    bump_smul_eq_self x₀ hδ hρ (hv i)]
  abel
end GroundTheory.Automorphic.Sobolev
