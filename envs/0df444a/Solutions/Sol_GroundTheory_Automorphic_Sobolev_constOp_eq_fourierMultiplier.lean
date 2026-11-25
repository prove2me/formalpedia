-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.constOp_eq_fourierMultiplier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:55.083249+00:00
-- url     : https://prove2.me/submissions/9a8a5ea7-ff1b-44bb-bf60-caf73ba578ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_iteratedLineDeriv_eq_fourierMultiplier
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
    constOp w c = fourierMultiplierCLM ℂ (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) := by
  have this : (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) =
      fun ξ ↦ ∑ i, c i * derivSymb (w i) ξ := by
    ext ξ; simp only [prinSymb, derivSymb_eq, Finset.mul_sum]
    congr 1; ext i; ring
  have hsum := fourierMultiplierCLM_sum ℂ (E := E) (g := fun i η ↦ c i * derivSymb (w i) η)
    (s := Finset.univ) (fun i _ ↦
      (Function.HasTemperateGrowth.const (c i)).mul (derivSymb_hasTemperateGrowth (w i)))
  beta_reduce at hsum
  rw [this, hsum]
  unfold constOp
  congr 1; ext1 i
  ext1 u
  rw [smul_apply, iteratedLineDerivOpCLM_apply, iteratedLineDeriv_eq_fourierMultiplier,
    show (fun η ↦ c i * derivSymb (w i) η) = c i • derivSymb (w i) from rfl,
    fourierMultiplierCLM_smul (derivSymb_hasTemperateGrowth (w i)), smul_apply]
end GroundTheory.Automorphic.Sobolev
