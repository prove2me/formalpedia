-- Prove2me | solution 1 for GlobalTheory.exists_equiv_of_sum_min_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:11.803868+00:00
-- url     : https://prove2.me/submissions/8bed390d-2827-4acc-8c25-156556da94ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamily
import Theorems.Thm_GlobalTheory_sum_min_succ_eq_add_card
import Theorems.Thm_GlobalTheory_card_gt_eq_card_eq_add_card_gt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ),
    (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) →
    ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by
  intro d d' e e' he he' h
  have h1 : ∀ j, (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => j < e' i)).card := by
    intro j
    have a := sum_min_succ_eq_add_card e j
    have b := sum_min_succ_eq_add_card e' j
    have c := h j
    have c' := h (j + 1)
    omega
  have h2 : ∀ j, Fintype.card {i // e i = j} = Fintype.card {i // e' i = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases j with _ | j
    · rw [Finset.filter_false_of_mem (fun i _ => (he i).ne'),
        Finset.filter_false_of_mem (fun i _ => (he' i).ne')]
      simp
    · have a := card_gt_eq_card_eq_add_card_gt e j
      have b := card_gt_eq_card_eq_add_card_gt e' j
      have c := h1 j
      have c' := h1 (j + 1)
      omega
  exact ⟨Equiv.ofFiberEquiv (f := e) (g := e') (fun j => Fintype.equivOfCardEq (h2 j)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end GlobalTheory
