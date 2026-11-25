-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:04:07.522806+00:00
-- url     : https://prove2.me/submissions/efa4280b-b3fb-45a3-8e4a-fee397245fcf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_eq_zero_of_isVanishingOn
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
theorem _root_.solution {g : E → ℂ} (hg : g.HasTemperateGrowth) {V U : Set E} (hV : IsOpen V)
    (hg1 : ∀ x ∈ V, g x = 1) (hVU : Vᶜ ⊆ U) {z : 𝓢'(E, ℂ)} (hz : Distribution.IsVanishingOn z U) :
    smulLeftCLM ℂ g z = z := by
  have h1 : (fun x ↦ g x - 1).HasTemperateGrowth := hg.sub (Function.HasTemperateGrowth.const 1)
  have hts : tsupport (fun x ↦ g x - 1) ⊆ U := by
    refine (closure_minimal ?_ hV.isClosed_compl).trans hVU
    intro x hx hxV
    exact hx (by simp [hg1 x hxV])
  have h0 := smulLeftCLM_eq_zero_of_isVanishingOn h1 hz hts
  have e : smulLeftCLM ℂ (fun x ↦ g x - 1) z = smulLeftCLM ℂ g z - z := by
    rw [show (fun x ↦ g x - 1) = g - fun _ ↦ (1 : ℂ) from rfl,
      smulLeftCLM_sub hg (Function.HasTemperateGrowth.const 1), sub_apply, smulLeftCLM_const,
      one_smul]
  rw [e, sub_eq_zero] at h0
  exact h0
end GroundTheory.Automorphic.Sobolev
