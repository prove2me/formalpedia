-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memLp_two_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:29.967872+00:00
-- url     : https://prove2.me/submissions/64fb42e1-6ec1-47c2-990b-f8a67e8c40b3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
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
variable {s N : ℝ} (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (φ : 𝓢(E, ℂ)) (G : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun p : E × E ↦ φ p.1 * G p.2) 2 ((volume : Measure E).prod volume) := by
  have hφ := (φ.memLp 2 (volume : Measure E))
  have hG := Lp.memLp G
  have hm : AEStronglyMeasurable (fun p : E × E ↦ φ p.1 * G p.2)
      ((volume : Measure E).prod volume) :=
    (φ.continuous.aestronglyMeasurable.comp_fst).mul (hG.1.comp_snd)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h1 := (memLp_two_iff_integrable_sq_norm hφ.1).1 hφ
  have h2 := (memLp_two_iff_integrable_sq_norm hG.1).1 hG
  refine (h1.mul_prod h2).congr (ae_of_all _ fun p ↦ ?_)
  simp [mul_pow]
end GroundTheory.Automorphic.Sobolev
