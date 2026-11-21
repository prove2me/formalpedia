-- Prove2me | solution 1 for GwExact.exists_rank_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:48.836829+00:00
-- url     : https://prove2.me/submissions/82d9954f-bd0a-4147-92da-b8d22c6df310

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
public import Theorems.Thm_GwExact_firstPos_spec
public import Theorems.Thm_GwExact_firstPos_le
public import Theorems.Thm_GwExact_numCols_zero
public import Theorems.Thm_GwExact_numCols_succ_of_mem
public import Theorems.Thm_GwExact_numCols_succ_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open GwExact
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
namespace GwExact
theorem _root_.solution : ∀ m, 1 ≤ numCols f m → ∃ j < m, rank f j + 1 = numCols f m := by
  intro m
  induction m with
  | zero =>
    intro h
    rw [numCols_zero] at h
    omega
  | succ m ih =>
    intro h
    by_cases hm : f m ∈ (Finset.range m).image f
    · rw [numCols_succ_of_mem f hm] at h ⊢
      obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, by omega, hj'⟩
    · refine ⟨m, by omega, ?_⟩
      have hfm : firstPos f m = m := by
        apply le_antisymm (firstPos_le f m)
        by_contra hlt
        exact hm (Finset.mem_image.mpr
          ⟨firstPos f m, Finset.mem_range.mpr (by omega), firstPos_spec f m⟩)
      rw [numCols_succ_of_notMem f hm, rank, hfm]
end GwExact
