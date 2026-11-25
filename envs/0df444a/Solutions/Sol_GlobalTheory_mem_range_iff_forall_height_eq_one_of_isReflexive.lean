-- Prove2me | solution 1 for GlobalTheory.mem_range_iff_forall_height_eq_one_of_isReflexive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:45.927838+00:00
-- url     : https://prove2.me/submissions/32249da4-b84d-4013-b634-f376a2a7a19d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_of_forall_height_eq_one_of_isReflexive
import Theorems.Thm_GlobalTheory_isTorsionFree_of_isLocalizedModule
import Theorems.Thm_GlobalTheory_injective_of_isLocalizedModule_nonZeroDivisors

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
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] (v : V) :
    v ∈ LinearMap.range f ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f := by
  refine ⟨fun hv p _ _ => ⟨1, (Ideal.ne_top_iff_one p).mp Ideal.IsPrime.ne_top', by simpa⟩,
    fun h => ?_⟩
  have := isTorsionFree_of_isLocalizedModule f
  obtain ⟨⟨m, a⟩, e⟩ := IsLocalizedModule.surj A⁰ f v
  exact mem_range_of_forall_height_eq_one_of_isReflexive f
    (injective_of_isLocalizedModule_nonZeroDivisors f) (nonZeroDivisors.ne_zero a.2) ⟨m, e.symm⟩
    fun p _ hp _ => h p hp
end GlobalTheory
