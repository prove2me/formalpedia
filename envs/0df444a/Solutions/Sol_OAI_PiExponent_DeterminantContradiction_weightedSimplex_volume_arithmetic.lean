-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:39:21.513996+00:00
-- url     : https://prove2.me/submissions/f400e1e7-56c2-4b2b-a333-a480a2a456a6

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (B : Real) (hB : 0 < B) :
    (∏ i, ENNReal.ofReal (1 / (w i / B))) *
        ENNReal.ofReal (1 / (n.factorial : Real)) =
      ENNReal.ofReal
        (B ^ n / ((n.factorial : Real) * Finset.univ.prod w)) := by
  have hfac : 0 < (n.factorial : Real) := by positivity
  have hwprod : 0 < ∏ i : Fin n, w i := Finset.prod_pos fun i hi => hw i
  have hmap :
      (∏ i : Fin n, ENNReal.ofReal (1 / (w i / B))) =
        ENNReal.ofReal (∏ i : Fin n, 1 / (w i / B)) := by
    classical
    have hgen (s : Finset (Fin n)) :
        (∏ i ∈ s, ENNReal.ofReal (1 / (w i / B))) =
          ENNReal.ofReal (∏ i ∈ s, 1 / (w i / B)) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        have hp : 0 ≤ 1 / (w a / B) := by
          have hwa : 0 < w a := hw a
          positivity
        rw [ENNReal.ofReal_mul hp, ih]
    simpa using hgen Finset.univ
  have hterm (i : Fin n) : 1 / (w i / B) = B / w i := by
    field_simp [ne_of_gt (hw i), ne_of_gt hB]
  have hprod :
      (∏ i : Fin n, B / w i) = B ^ n / ∏ i : Fin n, w i := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin]
  have hBprod : 0 < ∏ i : Fin n, B / w i :=
    Finset.prod_pos fun i hi => div_pos hB (hw i)
  rw [hmap]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_mul (le_of_lt hBprod)]
  congr 1
  calc
    (∏ i : Fin n, B / w i) * (1 / (n.factorial : Real)) =
        (B ^ n / ∏ i : Fin n, w i) * (1 / (n.factorial : Real)) := by rw [hprod]
    _ = B ^ n / ((n.factorial : Real) * ∏ i : Fin n, w i) := by
      field_simp [ne_of_gt hfac, ne_of_gt hwprod]
