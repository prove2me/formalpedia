-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.eq_zero_of_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:40.839406+00:00
-- url     : https://prove2.me/submissions/163081da-851a-4e4f-9ca7-94c9d8848588

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_neg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_mem
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
    {v : 𝓢'(E, ℂ)} (hv : MemSobolev s 2 v) (h : v + K v = 0) : v = 0 := by
  have e : v = -K v := eq_neg_of_add_eq_zero_left h
  have h1 : sob s v ≤ ENNReal.ofReal (1 / 2) * sob s v := by
    calc sob s v = sob s (-K v) := by rw [← e]
      _ = sob s (K v) := sob_neg _
      _ ≤ _ := hK v hv
  rw [sob_of_mem hv, ← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num)] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hx : ‖(SobolevSpace.mk v hv : SobolevSpace E ℂ s)‖ = 0 := by
    linarith [norm_nonneg (SobolevSpace.mk v hv : SobolevSpace E ℂ s)]
  have := congrArg SobolevSpace.toDistribution (norm_eq_zero.1 hx)
  simpa using this
end GroundTheory.Automorphic.Sobolev
