-- Prove2me | solution 1 for GlobalTheory.invertible_of_bijective_toSpanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:08.749894+00:00
-- url     : https://prove2.me/submissions/c19054fd-442c-4ba2-93ef-b8d68a82ced8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module A M] {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) : Module.Invertible A M :=
  .congr (LinearEquiv.ofBijective _ he)
end GlobalTheory
