-- Prove2me | solution 1 for LatinQuarter.clue_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:18.403608+00:00
-- url     : https://prove2.me/submissions/176aae4f-734d-4301-ad14-d979f5a32696

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Budget
public import Theorems.Thm_LatinQuarter_quarter_eq
public import Theorems.Thm_LatinQuarter_sum_free_columns
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
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (hP : P.card < n * n / 4) :
    (n - n / 2) * (n - n / 2) <
      ∑ r, (Fintype.card (FreeColumn P r) - n / 2) := by
  have hs := sum_free_columns P
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun r => Fintype.card (FreeColumn P r))
    (g := fun r => Fintype.card (FreeColumn P r) - n / 2 + n / 2)
    (fun r _ => by omega)
  rw [Finset.sum_add_distrib] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  rw [quarter_eq] at hP
  have hk : n / 2 ≤ n := by omega
  have hn : n = n / 2 + (n - n / 2) := by omega
  nlinarith
end LatinQuarter
