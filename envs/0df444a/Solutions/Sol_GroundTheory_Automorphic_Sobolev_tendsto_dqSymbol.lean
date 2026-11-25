-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.tendsto_dqSymbol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:35.801173+00:00
-- url     : https://prove2.me/submissions/1e5a523d-a2b6-4736-8e06-3bd206a6bb5c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
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
open Filter Topology
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (v ξ : E) :
    Tendsto (fun t ↦ dqSymbol v t ξ) (𝓝[≠] 0)
      (𝓝 ((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ))) := by
  set a : ℝ := 2 * Real.pi * inner ℝ ξ v
  have hf : HasDerivAt (fun t : ℝ ↦ Complex.exp (Complex.I * ((t * a : ℝ) : ℂ)))
      (Complex.I * a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.const_mul Complex.I).cexp
    simpa using this
  have h := hasDerivAt_iff_tendsto_slope_zero.1 hf
  have e : ∀ t : ℝ, t⁻¹ • (Complex.exp (Complex.I * (((0 + t) * a : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (((0 : ℝ) * a : ℝ) : ℂ))) = dqSymbol v t ξ := by
    intro t
    rw [dqSymbol, expChar, inner_smul_right, Complex.real_smul, zero_add, zero_mul,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    simp only [a]
    congr 3
    push_cast
    ring
  simp_rw [e] at h
  convert h using 2
  simp only [a]; push_cast; ring
end GroundTheory.Automorphic.Sobolev
