-- Prove2me | solution 1 for LeightonRao.BadExample.min_cut_ge
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:16:24.040464+00:00
-- url     : https://prove2.me/submissions/ba08ae38-ce48-450d-81eb-d0e6b2d7b425

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators
open LeightonRao.BadExample

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 < c) (hexp : IsEdgeExpander G c)
    (hn : 2 ≤ Fintype.card V) :
    c / ((Fintype.card V : ℝ) - 1) ≤ minCut (unitNetwork G) := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hV
  have hv : ({v} : Finset V)ᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hh := Finset.card_compl ({v} : Finset V)
    simp [he] at hh
    omega
  letI : Nonempty {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} :=
    ⟨⟨{v}, by simp, hv⟩⟩
  unfold minCut
  refine le_ciInf fun U => ?_
  have ha : 0 < U.val.card := U.property.1.card_pos
  have hb : 0 < U.valᶜ.card := U.property.2.card_pos
  have hs : U.val.card + U.valᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]; exact Nat.add_sub_of_le (Finset.card_le_univ _)
  have hnR : 0 < (Fintype.card V : ℝ) - 1 := by
    have : (1 : ℝ) < Fintype.card V := by exact_mod_cast (show 1 < Fintype.card V by omega)
    linarith
  have haR : 0 < (U.val.card : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (U.valᶜ.card : ℝ) := by exact_mod_cast hb
  have hsR : (U.val.card : ℝ) + (U.valᶜ.card : ℝ) = Fintype.card V := by exact_mod_cast hs
  have he := hexp U.val
  unfold ratioCost
  rw [le_div_iff₀ (mul_pos haR hbR), div_mul_eq_mul_div, div_le_iff₀ hnR]
  push_cast at he
  rcases le_total U.val.card U.valᶜ.card with hab | hba
  · rw [min_eq_left (by exact_mod_cast hab : (U.val.card : ℝ) ≤ U.valᶜ.card)] at he
    have hbnd : (U.valᶜ.card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
      have : (1 : ℝ) ≤ U.val.card := by exact_mod_cast ha
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hbnd (mul_nonneg hc.le haR.le),
      mul_le_mul_of_nonneg_right he hnR.le]
  · rw [min_eq_right (by exact_mod_cast hba : (U.valᶜ.card : ℝ) ≤ U.val.card)] at he
    have hbnd : (U.val.card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
      have : (1 : ℝ) ≤ U.valᶜ.card := by exact_mod_cast hb
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hbnd (mul_nonneg hc.le hbR.le),
      mul_le_mul_of_nonneg_right he hnR.le]

#print axioms solution
