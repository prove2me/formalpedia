-- Prove2me | solution 1 for GlobalTheory.free_of_invertible_of_finite_maximalSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:42.345405+00:00
-- url     : https://prove2.me/submissions/95d311da-bdbf-49c4-87af-c0b3b99507c8

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
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] : Module.Free A M :=
  Module.free_of_flat_of_finrank_eq _ _ 1
    fun _ ↦ let _ := @Ideal.Quotient.field A _; Module.Invertible.finrank_eq_one ..
end GlobalTheory
