-- Prove2me | solution 1 for GlobalTheory.mem_range_of_forall_height_eq_one_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:22.523839+00:00
-- url     : https://prove2.me/submissions/8583ace0-f4b4-46bf-a7a2-b75f43fad492

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_exists_smul_eq_of_forall_dual_dvd_of_projective
import Theorems.Thm_GlobalTheory_mem_range_of_forall_height_eq_one_of_dual

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
theorem _root_.solution [Module.Projective A M]
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V] {v : V} {a : A}
    (ha : a ≠ 0) (hav : a • v ∈ LinearMap.range f)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p →
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f) :
    v ∈ LinearMap.range f :=
  mem_range_of_forall_height_eq_one_of_dual
    (fun _ _ => exists_smul_eq_of_forall_dual_dvd_of_projective) f hf ha hav h
end GlobalTheory
