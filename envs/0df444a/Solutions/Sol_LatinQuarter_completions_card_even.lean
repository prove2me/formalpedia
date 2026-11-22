-- Prove2me | solution 1 for LatinQuarter.completions_card_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:45.8873+00:00
-- url     : https://prove2.me/submissions/6aa73052-6730-4659-bde8-a5fa2c699a32

module
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Theorems.Thm_LatinQuarter_coefficient_eq_card_latin_choices
public import Theorems.Thm_LatinQuarter_card_completions_eq
public import Theorems.Thm_LatinQuarter_small_clue_coefficient_zero


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (hL : IsLatin L) (hP : P.card < n * n / 4) :
    Even (completions P L).card := by
  let e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  have hc0 := small_clue_coefficient_zero P L e hP
  have hc1 := coefficient_eq_card_latin_choices P L hL
    (fun p => markedConstant e p.1 p.2)
  rw [hc0, ← card_completions_eq P L hL] at hc1
  exact ZMod.natCast_eq_zero_iff_even.mp hc1.symm
end LatinQuarter
