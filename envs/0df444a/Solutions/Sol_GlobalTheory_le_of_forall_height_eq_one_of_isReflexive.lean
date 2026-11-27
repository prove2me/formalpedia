-- Prove2me | solution 1 for GlobalTheory.le_of_forall_height_eq_one_of_isReflexive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:40.431687+00:00
-- url     : https://prove2.me/submissions/7ea9a250-e799-4c34-ab2d-6dba21828fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_range_of_forall_height_eq_one_of_isReflexive

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
theorem _root_.solution [Module.IsTorsionFree A V]
    {N N' : Submodule A V} [Module.IsReflexive A N']
    (h₀ : ∀ v ∈ N, ∃ a : A, a ≠ 0 ∧ a • v ∈ N')
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∀ v ∈ N, ∃ s, s ∉ p ∧ s • v ∈ N') :
    N ≤ N' := fun v hv => by
  obtain ⟨a, ha, hav⟩ := h₀ v hv
  simpa using mem_range_of_forall_height_eq_one_of_isReflexive N'.subtype N'.subtype_injective
    (v := v) ha (by simpa) fun p _ hp _ => by simpa using h p hp v hv
end GlobalTheory
