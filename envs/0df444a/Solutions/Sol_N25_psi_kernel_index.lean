-- Prove2me | solution 1 for N25.psi_kernel_index
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:44.970847+00:00
-- url     : https://prove2.me/submissions/c4ab4ff8-768f-4edc-9520-803ffd42d491

import Mathlib
import Theorems.Thm_N25_psiBar_ker
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_N25_psi_inertia_witness
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_N25_level25_subgroup_card

set_option autoImplicit false

namespace N25

/-- The kernel of the actual absolute Galois character has index five.
Surjectivity onto the five character values follows from the explicit inertia
element at 5, so no surjectivity assumption on chi25 is needed. -/
theorem _root_.solution : psi.ker.index = 5 := by
  obtain ⟨τ, _, hτ⟩ := psi_inertia_witness
  have hpowers : ∀ u : (ZMod 25)ˣ, ∃ n : Fin 5,
      psiBar u = (ZMod.unitOfCoprime 57 (by decide)) ^ n.val := by decide
  have hrange : psi.range = psiBar.range := by
    ext u
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨chi25 σ, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨n, hn⟩ := hpowers v
      refine ⟨(r5 τ) ^ n.val, ?_⟩
      rw [map_pow, hτ, ← hn]
  rw [Subgroup.index_ker, hrange, ← Subgroup.index_ker, psiBar_ker]
  have h := H25.index_mul_card
  have hcard : Nat.card (ZMod 25)ˣ = 20 := by
    norm_num [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  rw [level25_subgroup_card, hcard] at h
  omega

end N25
