-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_volume_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:10:51.287523+00:00
-- url     : https://prove2.me/submissions/31de72ca-3c5b-4c79-aed2-95fa8694cade

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_diagonal_scaling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    ENNReal.toReal
      (MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T})
      = T ^ n / ((n.factorial : Real) * Finset.univ.prod w) := by
  classical
  have hstd :=
    OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume
      n T hT
  have hscale :=
    OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_diagonal_scaling
      n w hw T hT
  have hprod : 0 < ∏ i : Fin n, w i := Finset.prod_pos fun i _ => hw i
  rw [hscale, hstd]
  have hfactor : 0 ≤ 1 / ∏ i : Fin n, w i := by positivity
  have hsimplex : 0 ≤ T ^ n / (n.factorial : Real) := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfactor,
    ENNReal.toReal_ofReal hsimplex]
  have hfact : (n.factorial : Real) ≠ 0 := by positivity
  field_simp [hprod.ne', hfact]
  <;> ring