-- Prove2me | solution 1 for GwExact.goodPos_of_colouring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:25:07.153181+00:00
-- url     : https://prove2.me/submissions/d449b900-124b-4950-9120-8e96a91f2021

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_rank_eq_iff
public import Theorems.Thm_GwExact_rank_zero
public import Theorems.Thm_GwExact_rank_pred
public import Theorems.Thm_GwExact_rank_lt_card

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r R l n : ℕ} (hrR : r ≤ R) (c : ℕ → Fin r)
    (hrb : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
      ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d)))
    (hmono : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x) :
    GoodPos n R l (rank fun i => c (i + 1)) := by
  set f : ℕ → Fin r := fun i => c (i + 1) with hfdef
  have hf : ∀ i i', rank f i = rank f i' ↔ c (i + 1) = c (i' + 1) := fun i i' => rank_eq_iff f
  refine ⟨fun i => lt_of_lt_of_le (rank_lt_card f i) hrR, rank_zero f, ?_, ?_, ?_⟩
  · intro i hi
    exact rank_pred f hi
  · intro a d hd had
    by_contra hcon
    push Not at hcon
    apply hmono (a + 1) d (by omega) hd (by omega)
    intro j hj
    have h2 := (hf (a + j * d) a).mp (hcon j hj)
    rwa [show a + j * d + 1 = a + 1 + j * d by omega] at h2
  · intro a d hd had hall
    apply hrb (a + 1) d (by omega) hd (by omega)
    obtain ⟨h1, h2, h3⟩ := hall
    refine ⟨fun h => h1 ((hf _ _).mpr ?_), fun h => h2 ((hf _ _).mpr ?_),
      fun h => h3 ((hf _ _).mpr ?_)⟩
    · rwa [show a + d + 1 = a + 1 + d by omega]
    · rwa [show a + 2 * d + 1 = a + 1 + 2 * d by omega]
    · rwa [show a + d + 1 = a + 1 + d by omega, show a + 2 * d + 1 = a + 1 + 2 * d by omega]
end GwExact
