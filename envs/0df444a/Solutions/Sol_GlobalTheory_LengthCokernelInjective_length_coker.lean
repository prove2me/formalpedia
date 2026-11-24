-- Prove2me | solution 1 for GlobalTheory.LengthCokernelInjective.length_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:22.086369+00:00
-- url     : https://prove2.me/submissions/4f8d5f8f-152d-4852-92d0-34a9e62dac8c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Theorems.Thm_GlobalTheory_LengthCokernelInjective_length_coker_of_injective
import Theorems.Thm_GlobalTheory_LengthCokernelInjective_length_coker_of_not_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthCokernelInjective
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.LengthCokernelInjective
theorem _root_.solution (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.ker f = ⊥
  · exact length_coker_of_injective f (LinearMap.ker_eq_bot.mp hf)
  · rw [length_coker_of_not_injective f hf, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf]
    simp
end GlobalTheory.LengthCokernelInjective
