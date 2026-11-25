-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.HasOrder.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:41.688237+00:00
-- url     : https://prove2.me/submissions/e00796ba-0d04-4c7a-b0c9-499da35dbc9b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_zero
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add
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
open GroundTheory.Automorphic.Sobolev.HasOrder
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {k k₁ k₂ : ℝ}
namespace GroundTheory.Automorphic.Sobolev.HasOrder
theorem _root_.solution {ι : Type*} (S : Finset ι) {T : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (h : ∀ i ∈ S, HasOrder (T i) k) : HasOrder (∑ i ∈ S, T i) k := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using zero k
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
end GroundTheory.Automorphic.Sobolev.HasOrder
