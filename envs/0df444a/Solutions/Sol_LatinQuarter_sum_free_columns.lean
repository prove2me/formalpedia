-- Prove2me | solution 1 for LatinQuarter.sum_free_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:41.368169+00:00
-- url     : https://prove2.me/submissions/23750680-8ca2-475c-a5eb-8a2c0dc111a2

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Budget
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_one
attribute [local simp] LatinQuarter.mem_completions



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n)) :
    (∑ r, Fintype.card (FreeColumn P r)) + P.card = n * n := by
  classical
  let e : ((r : Fin n) × FreeColumn P r) ≃ {p : Cell n // p ∉ P} :=
    { toFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      invFun := fun x => ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_sigma, Fintype.card_subtype_compl] at hc
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hc
  have hp : P.card ≤ n * n := by
    simpa using (Finset.card_le_univ P)
  omega
end LatinQuarter
