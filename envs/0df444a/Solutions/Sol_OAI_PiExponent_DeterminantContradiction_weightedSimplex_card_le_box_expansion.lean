-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_box_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:05:46.725021+00:00
-- url     : https://prove2.me/submissions/4573771d-7bbd-4701-a793-18d4662c538e

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_expandedRegion_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_expandedWeightedSimplex_volume
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n -> Real) (hw : (i : Fin n) -> 0 < w i) (H : Real) (hH : 0 <= H) :
    ((strictWeightedSimplex w H).card : Real) <=
      (H + Finset.univ.sum w) ^ n /
        ((n.factorial : Real) * Finset.univ.prod w) := by
  let R : Real :=
    (H + Finset.univ.sum w) ^ n /
      ((n.factorial : Real) * Finset.univ.prod w)
  have hsum : 0 <= Finset.univ.sum w :=
    Finset.sum_nonneg fun i hi => le_of_lt (hw i)
  have hbase : 0 <= H + Finset.univ.sum w := add_nonneg hH hsum
  have hden : 0 < (n.factorial : Real) * Finset.univ.prod w :=
    mul_pos (by exact_mod_cast Nat.factorial_pos n)
      (Finset.prod_pos fun i hi => hw i)
  have hR : 0 <= R := by
    dsimp [R]
    exact div_nonneg (pow_nonneg hbase n) (le_of_lt hden)
  have hcard : 0 <= ((strictWeightedSimplex w H).card : Real) :=
    Nat.cast_nonneg _
  have hmeasure :=
    OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expandedRegion_volume
      n w hw H hH
  rw [OAI.PiExponent.DeterminantContradiction.expandedWeightedSimplex_volume
    n w hw H hH] at hmeasure
  have hreal :
      ((strictWeightedSimplex w H).card : Real) <= R := by
    exact (ENNReal.ofReal_le_ofReal_iff hR).mp hmeasure
  simpa [R] using hreal