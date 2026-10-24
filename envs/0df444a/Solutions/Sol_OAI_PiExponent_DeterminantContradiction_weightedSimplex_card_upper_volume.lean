-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:06:13.433987+00:00
-- url     : https://prove2.me/submissions/e5947d82-27a9-4a8d-8030-87dc6993d50e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_expanded_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_normalize_expanded_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A H : Real)
    (hw : ∀ i, 0 < w i) (hH : 0 < H)
    (hcut : (∑ i : Fin m, w i) / H < A) :
    ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤
      (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  have hsum : 0 ≤ ∑ i : Fin m, w i :=
    Finset.sum_nonneg fun i hi => (hw i).le
  have hA : 0 < A := lt_of_le_of_lt (div_nonneg hsum hH.le) hcut
  have hB : 0 < A * H := mul_pos hA hH
  have hcard : ((realWeightedSimplex w (A * H)).card : Real) ≤
      (A * H + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
    exact weightedSimplex_card_le_expanded_volume w (A * H) hw hB
  exact weightedSimplex_normalize_expanded_bound w A H hw hH hcut hcard