-- Prove2me | solution 1 for N4Code.dRow_replace_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:01.582764+00:00
-- url     : https://prove2.me/submissions/3d798fc9-6310-45f7-928d-3f63e65f00b1

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_hammingDist_set_bit
import Theorems.Thm_N4Code_dRow_eq_hammingDist


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (y : Word n) :
    ∀ i : Fin 4, dRow (replaceColumn C t s') i y =
      if s' i then dRow C i (flipBit t y) else dRow C i y := by
  intro i
  rw [dRow_eq_hammingDist, dRow_eq_hammingDist]
  have hrow : row (replaceColumn C t s') i = fun u : Fin n => if u = t then s' i else row C i u := by
    funext u
    by_cases ht : u = t <;> simp [row, replaceColumn, colBit, ht]
  rw [hrow]
  have ht0 : (row C i) t = false := by
    unfold row
    simp [hcol, colBit, col0]
  by_cases hb : s' i = true
  · have hd := hammingDist_set_bit (row C i) t y (s' i) ht0
    rw [hd, hb]
    simp
  · have hs'f : s' i = false := by
      by_contra h
      have htrue : s' i = true := by
        cases hs : s' i
        · exfalso
          exact h hs
        · simp
      exact hb htrue
    have hd := hammingDist_set_bit (row C i) t y (s' i) ht0
    rw [hd, hs'f]
    simp
    rw [dRow_eq_hammingDist]
end N4Code
