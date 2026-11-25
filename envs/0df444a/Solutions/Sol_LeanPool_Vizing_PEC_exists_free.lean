-- Prove2me | solution 1 for LeanPool.Vizing.PEC.exists_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:27:16.07014+00:00
-- url     : https://prove2.me/submissions/ba051678-b470-4bda-a70f-b612f2858fe4

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
variable {V : Type*} [DecidableEq V] {C : Type*}
open LeanPool.Vizing.PEC
variable {G : SimpleGraph V}
omit [DecidableEq V]
namespace LeanPool.Vizing.PEC
theorem _root_.solution [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree < Fintype.card C)
    (v : V) : ∃ γ, c.IsFree v γ := by
  by_contra hcon
  push Not at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hginj : Set.InjOn g (univ : Finset C) := by
    intro γ₁ _ γ₂ _ h
    have : (some γ₁ : Option C) = some γ₂ := by rw [← hg γ₁, ← hg γ₂, h]
    exact Option.some_injective _ this
  have hmem : ∀ γ ∈ (univ : Finset C), g γ ∈ G.neighborFinset v := by
    intro γ _
    exact (mem_neighborFinset _ _ _).2 (c.col_adj (hg γ))
  have hcards := Finset.card_le_card_of_injOn g hmem hginj
  simp only [card_univ, card_neighborFinset_eq_degree] at hcards
  exact absurd (hcards.trans (G.degree_le_maxDegree v)) (by omega)
end LeanPool.Vizing.PEC
