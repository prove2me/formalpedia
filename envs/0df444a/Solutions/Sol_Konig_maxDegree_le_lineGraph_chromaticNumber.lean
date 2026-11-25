-- Prove2me | solution 1 for Konig.maxDegree_le_lineGraph_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:35:36.498724+00:00
-- url     : https://prove2.me/submissions/31380417-7e11-4170-ad40-bc28d21ebecb

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
namespace Konig
theorem _root_.solution [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.maxDegree : ℕ∞) ≤ G.lineGraph.chromaticNumber := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have : G.maxDegree = 0 := by
      rw [← Nat.le_zero]
      exact G.maxDegree_le_of_forall_degree_le 0 (fun v => isEmptyElim v)
    rw [this, Nat.cast_zero]
    exact zero_le
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    refine le_chromaticNumber_of_pairwise_adj (ι := G.neighborSet v) ?_
      (fun u => (⟨s(v, u), u.2⟩ : G.edgeSet)) ?_
    · rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
    · intro u u' huu
      rw [lineGraph_adj_iff_exists]
      refine ⟨fun h => huu (Subtype.ext ?_), v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      have : (u : V) = u' ∨ v = u' ∧ (u : V) = v := by simpa using congrArg Subtype.val h
      rcases this with h' | ⟨-, h'⟩
      · exact h'
      · exact absurd h' (G.ne_of_adj u.2).symm
end Konig
