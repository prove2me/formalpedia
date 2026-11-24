-- Prove2me | solution 1 for GlobalTheory.exists_idempotent_lift_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:22.339381+00:00
-- url     : https://prove2.me/submissions/7f6c798f-4f78-4687-bb14-68ac26f27282

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_idempotent_eq_of_forall_isMaximal
import Theorems.Thm_GlobalTheory_exists_idempotent_notMem_iff_mem_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type*) {S C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [CommRing C]
    (π : S →+* C) (hπ : Function.Surjective π) {c : C} (hc : IsIdempotentElem c) :
    ∃ e : S, IsIdempotentElem e ∧ π e = c := by
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_mem_of_henselian R (S := S)
    {n | ∃ m : Ideal C, m.IsMaximal ∧ m.comap π = n.asIdeal ∧ c ∉ m}
  refine ⟨e, he, idempotent_eq_of_forall_isMaximal (he.map π) hc fun m hm ↦ ?_⟩
  have := H ⟨m.comap π, Ideal.comap_isMaximal_of_surjective π hπ⟩
  rw [← not_iff_not]
  refine this.trans ⟨?_, fun h ↦ ⟨m, hm, rfl, h⟩⟩
  rintro ⟨m', -, h1, h2⟩
  rwa [← Ideal.comap_injective_of_surjective π hπ h1]
end GlobalTheory
