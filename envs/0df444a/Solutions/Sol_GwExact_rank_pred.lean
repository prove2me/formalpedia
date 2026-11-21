-- Prove2me | solution 1 for GwExact.rank_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:24.671065+00:00
-- url     : https://prove2.me/submissions/6ffc291d-e473-4efa-bd72-563347e9b3ae

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_firstPos_le
public import Theorems.Thm_GwExact_exists_rank_pred

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution {i : ℕ} (h : 1 ≤ rank f i) : ∃ j < i, rank f j + 1 = rank f i := by
  obtain ⟨j, hj, hj'⟩ := exists_rank_pred f (firstPos f i) h
  exact ⟨j, lt_of_lt_of_le hj (firstPos_le f i), hj'⟩
end GwExact
