-- Prove2me | solution 1 for GlobalTheory.existsUnique_idempotent_lift_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:49.757878+00:00
-- url     : https://prove2.me/submissions/6c87d32b-4ed0-4f65-9f8b-c5e7803d7497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_idempotent_eq_of_sub_mem_jacobson
import Theorems.Thm_GlobalTheory_exists_idempotent_lift_of_henselian

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
    (π : S →+* C) (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ (⊥ : Ideal S).jacobson)
    {c : C} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ π e = c := by
  obtain ⟨e, he, h⟩ := exists_idempotent_lift_of_henselian R π hπ hc
  refine ⟨e, ⟨he, h⟩, fun e' ⟨he', h'⟩ ↦ idempotent_eq_of_sub_mem_jacobson he' he (hker ?_)⟩
  rw [RingHom.mem_ker, map_sub, h, h', sub_self]
end GlobalTheory
