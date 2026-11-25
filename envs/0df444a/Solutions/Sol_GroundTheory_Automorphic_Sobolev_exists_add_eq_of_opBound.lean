-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_add_eq_of_opBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:44.103994+00:00
-- url     : https://prove2.me/submissions/307357e7-ad3c-4364-96df-622b3443b1d9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_memSobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_memSobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_memSobolev_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
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
theorem _root_.solution {K : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s : ℝ} (hK : OpBound K s s (1 / 2))
    {z : 𝓢'(E, ℂ)} (hz : MemSobolev s 2 z) : ∃ v, MemSobolev s 2 v ∧ v + K v = z := by
  have hmem : ∀ v : SobolevSpace E ℂ s, MemSobolev s 2 (z - K (SobolevSpace.toDistribution v)) :=
    fun v ↦ (SobolevSpace.exists_toDistribution_eq_iff _).1
      ⟨SobolevSpace.mk z hz - SobolevSpace.mk _ (hK.memSobolev (SobolevSpace.memSobolev_toDistribution v)),
        by simp⟩
  let f : SobolevSpace E ℂ s → SobolevSpace E ℂ s := fun v ↦ SobolevSpace.mk _ (hmem v)
  have hf : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun v v' ↦ ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have e : f v - f v' = SobolevSpace.mk (K (SobolevSpace.toDistribution (v' - v)))
        (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)) := by
      apply SobolevSpace.toDistribution_injective
      simp [f, map_sub]
    rw [e]
    have h := hK _ (SobolevSpace.memSobolev_toDistribution (v' - v))
    rw [sob_of_mem (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)), sob_toDistribution,
      ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    rw [norm_sub_rev] at h'
    simpa using h'
  obtain ⟨v, hv⟩ : ∃ v, f v = v := ⟨_, hf.fixedPoint_isFixedPt (f := f)⟩
  refine ⟨SobolevSpace.toDistribution v, SobolevSpace.memSobolev_toDistribution v, ?_⟩
  have := congrArg SobolevSpace.toDistribution hv
  simp only [f, SobolevSpace.toDistribution_mk] at this
  exact eq_sub_iff_add_eq.1 this.symm
end GroundTheory.Automorphic.Sobolev
