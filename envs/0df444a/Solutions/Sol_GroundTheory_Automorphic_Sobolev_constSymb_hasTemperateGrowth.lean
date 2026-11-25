-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.constSymb_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:37.928737+00:00
-- url     : https://prove2.me/submissions/b3d17726-2ec6-470e-82a1-df93673de1e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_eq
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
variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (c : ι → ℂ) :
    (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ).HasTemperateGrowth := by
  have : (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) =
      fun ξ ↦ ∑ i, c i * derivSymb (w i) ξ := by
    ext ξ; simp only [prinSymb, derivSymb_eq, Finset.mul_sum]; congr 1; ext i; ring
  rw [this]
  exact Function.HasTemperateGrowth.sum fun i _ ↦
    (Function.HasTemperateGrowth.const (c i)).mul (derivSymb_hasTemperateGrowth (w i))
end GroundTheory.Automorphic.Sobolev
