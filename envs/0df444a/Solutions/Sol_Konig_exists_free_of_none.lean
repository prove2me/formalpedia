-- Prove2me | solution 1 for Konig.exists_free_of_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:31:45.707789+00:00
-- url     : https://prove2.me/submissions/d13f1b0e-ba83-401a-85e7-d3622a647d69

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
theorem _root_.solution [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) : ∃ γ, c.IsFree x γ := by
  classical
  by_contra hcon
  push Not at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hginj : Set.InjOn g (univ : Finset C) := by
    intro γ₁ _ γ₂ _ h
    have : (some γ₁ : Option C) = some γ₂ := by rw [← hg γ₁, ← hg γ₂, h]
    exact Option.some_injective _ this
  have hmem : ∀ γ ∈ (univ : Finset C), g γ ∈ (G.neighborFinset x).erase y := by
    intro γ _
    refine Finset.mem_erase.2 ⟨fun h => ?_, (mem_neighborFinset _ _ _).2 (c.col_adj (hg γ))⟩
    have := hg γ
    rw [h, hnone] at this
    simp at this
  have hcards := Finset.card_le_card_of_injOn g hmem hginj
  rw [card_univ, Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 hadj),
    card_neighborFinset_eq_degree] at hcards
  have hdeg := G.degree_le_maxDegree x
  have hpos : 0 < G.degree x := G.degree_pos_iff_exists_adj x |>.2 ⟨y, hadj⟩
  omega
end Konig
