-- Prove2me | solution 1 for GwExact.rank_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:52.4442+00:00
-- url     : https://prove2.me/submissions/85481154-0863-4038-bc61-6061d3234120

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_ne_of_lt_firstPos

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r : ℕ} (f : ℕ → Fin r) (i : ℕ) : rank f i < r := by
  have hsub : (Finset.range (firstPos f i)).image f ⊆ Finset.univ.erase (f i) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_erase.mpr ⟨ne_of_lt_firstPos f (Finset.mem_range.mp hj), Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  have h2 : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) (f i).isLt
  unfold rank numCols
  omega
end GwExact
