-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:58.548174+00:00
-- url     : https://prove2.me/submissions/aea94c97-f072-4128-a9fe-ecaf89a1c4ef

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_not_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (c : ℂ) (u : 𝓢'(E, ℂ)) : sob s (c • u) ≤ ‖c‖ₑ * sob s u := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (0 : ℂ) • u = 0 := zero_smul ℂ u
    rw [h0, sob_zero]; exact zero_le
  by_cases hu : MemSobolev s 2 u
  · obtain ⟨u', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
    rw [← SobolevSpace.toDistribution_smul, sob_toDistribution, sob_toDistribution, enorm_smul]
  · rw [sob_of_not_mem hu, ENNReal.mul_top (by simpa using hc)]; exact le_top
end GroundTheory.Automorphic.Sobolev
