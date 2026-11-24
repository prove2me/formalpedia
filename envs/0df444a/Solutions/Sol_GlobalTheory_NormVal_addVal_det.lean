-- Prove2me | solution 1 for GlobalTheory.NormVal.addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:00.852808+00:00
-- url     : https://prove2.me/submissions/17ff550a-b3d1-48b2-b08c-0cd5904c215d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_addVal_det_of_injective
import Theorems.Thm_GlobalTheory_NormVal_length_quot_range_of_not_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.NormVal
theorem _root_.solution (f : M →ₗ[R] M) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by
  by_cases hf : Function.Injective f
  · exact addVal_det_of_injective f hf
  · rw [length_quot_range_of_not_injective f hf, addVal_eq_top_iff,
      LinearMap.det_eq_zero_iff_ker_ne_bot, Ne, LinearMap.ker_eq_bot]
    exact hf
end GlobalTheory.NormVal
