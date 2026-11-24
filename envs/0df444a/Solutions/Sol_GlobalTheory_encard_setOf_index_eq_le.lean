-- Prove2me | solution 1 for GlobalTheory.encard_setOf_index_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:40.499709+00:00
-- url     : https://prove2.me/submissions/32eee6db-ff6d-4041-85fe-6f9819460bd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_encard_setOf_index_prime_le
import Theorems.Thm_GlobalTheory_exists_le_relIndex_eq_prime
import Theorems.Thm_GlobalTheory_encard_biUnion_le_mul
import Theorems.Thm_GlobalTheory_setOf_le_relIndex_eq_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.encard ≤ ((m ^ finrank ℤ M : ℕ) : ℕ∞) := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one =>
    have : {H : AddSubgroup M | H.index = 1} = {⊤} := by ext H; simp
    simp [this]
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := fun h => hm (by simp [h])
    have hsub : {H : AddSubgroup M | H.index = p * a} ⊆
        ⋃ K ∈ {K : AddSubgroup M | K.index = a}, {H | H ≤ K ∧ H.relIndex K = p} := by
      intro H hH
      have hH' : H.index = p * a := hH
      obtain ⟨K, hK, hr⟩ := exists_le_relIndex_eq_prime hp H (hH' ▸ hm) (hH' ▸ dvd_mul_right _ _)
      have := AddSubgroup.relIndex_mul_index hK
      rw [hr, hH'] at this
      exact Set.mem_biUnion (x := K) (Nat.eq_of_mul_eq_mul_left hp.pos this) ⟨hK, hr⟩
    refine (Set.encard_le_encard hsub).trans
      ((encard_biUnion_le_mul _ _ _ (p ^ finrank ℤ M) (ih ha) ?_).trans ?_)
    · intro K _
      rw [setOf_le_relIndex_eq_image]
      refine (Set.encard_image_le _ _).trans ?_
      haveI : Module.Finite ℤ K := inferInstanceAs (Module.Finite ℤ K.toIntSubmodule)
      haveI : Module.Free ℤ K := inferInstanceAs (Module.Free ℤ K.toIntSubmodule)
      refine (encard_setOf_index_prime_le hp).trans ?_
      have : finrank ℤ K ≤ finrank ℤ M := Submodule.finrank_le K.toIntSubmodule
      exact_mod_cast Nat.pow_le_pow_right hp.pos this
    · rw [mul_pow, mul_comm]
end GlobalTheory
