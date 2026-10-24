-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_explicit_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:39:55.575999+00:00
-- url     : https://prove2.me/submissions/9239582e-2c51-4bc3-b728-2b0e38063d26

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_lower_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_upper_volume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A H : Real)
    (hw : ∀ i, 0 < w i) (hH : 0 < H)
    (hcut : (∑ i : Fin m, w i) / H < A) :
    (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i ≤
      ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ∧
      ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤
        (A + (∑ i : Fin m, w i) / H) ^ m /
          ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  constructor
  · exact OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_volume
      w A H hw hH hcut
  · exact OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_volume
      w A H hw hH hcut