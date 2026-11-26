-- Prove2me | solution 1 for MurtySimon.sum_pieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:15.469256+00:00
-- url     : https://prove2.me/submissions/b3897a21-79bc-422e-9600-8d5432c22840

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
public import Theorems.Thm_MurtySimon_emb_mk
public import Theorems.Thm_MurtySimon_mem_Lt


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (M : Finset (Sym2 V)) (C : (aux G ∅).ConnectedComponent) :
    ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter (fun D => emb G M D = C),
      ((cA G M D : ℤ) - cB G M D) = (#((LC0 C).filter (· ∉ M)) : ℤ) - cB G ∅ C := by
  set F := (univ : Finset (aux G M).ConnectedComponent).filter (fun D => emb G M D = C)
  have hA : ∑ D ∈ F, cA G M D = #((LC0 C).filter (· ∉ M)) := by
    unfold cA
    have hs : (LC0 C).filter (· ∉ M) =
        (Lt G M).filter fun e => (aux G ∅).connectedComponentMk e = C := by
      ext e; simp only [mem_filter, mem_Lt, LC0]; tauto
    rw [hs, card_eq_sum_card_fiberwise (f := (aux G M).connectedComponentMk) (t := F)]
    · refine sum_congr rfl fun D hD => ?_
      congr 1
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        rw [← emb_mk, h2]; exact (mem_filter.1 hD).2
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · intro e he
      exact mem_filter.2 ⟨mem_univ _, by rw [emb_mk]; exact (mem_filter.1 he).2⟩
  have hB : ∑ D ∈ F, cB G M D = cB G ∅ C := by
    unfold cB
    rw [card_eq_sum_card_fiberwise (f := (aux G M).connectedComponentMk) (t := F)]
    · refine sum_congr rfl fun D hD => ?_
      congr 1
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        rw [← emb_mk, h2]; exact (mem_filter.1 hD).2
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · intro e he
      exact mem_filter.2 ⟨mem_univ _, by rw [emb_mk]; exact (mem_filter.1 he).2⟩
  rw [sum_sub_distrib]
  push_cast [← hA, ← hB]
  rfl
end MurtySimon
