-- Prove2me | solution 1 for MurtySimon.completeBipartiteGraph_isDiameterTwoCritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:23:31.950866+00:00
-- url     : https://prove2.me/submissions/7c8964d8-10de-453a-a3cf-24dcf6dc0902

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_two_le_edist
public import Theorems.Thm_MurtySimon_completeBipartiteGraph_no_common
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_OnPath_ne
public import Theorems.Thm_MurtySimon_ediam_le_two_iff


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution {n : ℕ} (hn : 3 ≤ n) :
    IsDiameterTwoCritical (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))) := by
  set H := completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))
  have hd : DiamLeTwo H := by
    intro p q hpq
    rcases p with p | p <;> rcases q with q | q
    · exact Or.inr ⟨Sum.inr ⟨0, by omega⟩, by simp [H], by simp [H]⟩
    · exact Or.inl (by simp [H])
    · exact Or.inl (by simp [H])
    · exact Or.inr ⟨Sum.inl ⟨0, by omega⟩, by simp [H], by simp [H]⟩
  refine ⟨le_antisymm ((ediam_le_two_iff H).2 hd) ?_, fun e he => ?_⟩
  · have h01 : (Sum.inl ⟨0, by omega⟩ : Fin ((n + 1) / 2) ⊕ Fin (n / 2)) ≠
        Sum.inl ⟨1, by omega⟩ := by simp
    exact (two_le_edist h01 (by simp [H])).trans (edist_le_ediam)
  · rw [← not_le, ediam_le_two_iff]
    intro hd'
    induction e using Sym2.ind with
    | h p q =>
      rw [mem_edgeSet] at he
      rcases hd' p q he.ne with h | ⟨w, h1, h2⟩
      · simp at h
      · simp only [deleteEdges_adj] at h1 h2
        exact completeBipartiteGraph_no_common he h1.1 h2.1
end MurtySimon
