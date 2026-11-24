-- Prove2me | solution 1 for GlobalTheory.height_eq_one_of_mem_associatedPrimes_coker_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:20.779487+00:00
-- url     : https://prove2.me/submissions/ab6a853b-a103-4213-8e79-1437bee618ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_minimalPrimes_span_singleton_of_height_eq_one
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
theorem _root_.solution
    (hM : ∀ {a : A}, a ≠ 0 → ∀ {m : M}, (∀ φ : Module.Dual A M, a ∣ φ m) → ∃ m', a • m' = m)
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V]
    (ht : ∀ v : V, ∃ a : A, a ≠ 0 ∧ a • v ∈ LinearMap.range f) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (V ⧸ LinearMap.range f)) : p.height = 1 := by
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hmem : ∀ r, r ∈ p ↔ r • v ∈ LinearMap.range f := fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  obtain ⟨a, ha, hav⟩ := ht v
  by_contra hne
  refine hpp.ne_top ((Ideal.eq_top_iff_one p).mpr ((hmem 1).mpr ?_))
  rw [one_smul]
  refine mem_range_of_forall_height_eq_one_of_dual hM f hf ha hav fun q _ hq haq => ?_
  by_contra! H
  have hle : p ≤ q := fun s hs => by_contra fun hsq => H s hsq ((hmem s).mp hs)
  have hge := (mem_minimalPrimes_span_singleton_of_height_eq_one hq ha haq).2
    ⟨hpp, (Ideal.span_singleton_le_iff_mem p).mpr ((hmem a).mpr hav)⟩ hle
  exact hne (le_antisymm hle hge ▸ hq)
end GlobalTheory
