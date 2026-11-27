-- Prove2me | solution 1 for GlobalTheory.height_eq_one_of_mem_associatedPrimes_coker_of_isReflexive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:52.849161+00:00
-- url     : https://prove2.me/submissions/8239afa7-8567-4e0d-8d7f-b6616c6332d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_exists_smul_eq_of_forall_dual_dvd_of_isReflexive
import Theorems.Thm_GlobalTheory_height_eq_one_of_mem_associatedPrimes_coker_of_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]
namespace GlobalTheory
theorem _root_.solution [Module.IsReflexive A M]
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V]
    (ht : ∀ v : V, ∃ a : A, a ≠ 0 ∧ a • v ∈ LinearMap.range f) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (V ⧸ LinearMap.range f)) : p.height = 1 :=
  height_eq_one_of_mem_associatedPrimes_coker_of_dual
    (fun ha _ => exists_smul_eq_of_forall_dual_dvd_of_isReflexive ha) f hf ht hp
end GlobalTheory
