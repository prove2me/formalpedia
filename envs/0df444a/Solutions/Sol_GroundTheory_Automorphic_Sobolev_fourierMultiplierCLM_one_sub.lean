-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourierMultiplierCLM_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:34.608743+00:00
-- url     : https://prove2.me/submissions/39a070a5-f96c-4f18-9334-7554dcd62edb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {r : E → ℂ} (hr : r.HasTemperateGrowth) :
    fourierMultiplierCLM ℂ (fun ξ ↦ 1 - r ξ) =
      ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - fourierMultiplierCLM ℂ r := by
  ext1 u
  rw [show (fun ξ ↦ 1 - r ξ) = (fun _ ↦ (1 : ℂ)) - r from rfl, fourierMultiplierCLM_apply,
    smulLeftCLM_sub (Function.HasTemperateGrowth.const 1) hr, sub_apply, smulLeftCLM_const,
    one_smul]
  have e : ∀ x y : 𝓢'(E, ℂ), 𝓕⁻ (x - y) = 𝓕⁻ x - 𝓕⁻ y := fun x y ↦ by
    rw [sub_eq_add_neg, FourierTransform.fourierInv_add, FourierTransform.fourierInv_neg,
      ← sub_eq_add_neg]
  rw [e, FourierTransform.fourierInv_fourier_eq, sub_apply, fourierMultiplierCLM_apply]
  rfl
end GroundTheory.Automorphic.Sobolev
