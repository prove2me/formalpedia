-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:55:10.304294+00:00
-- url     : https://prove2.me/submissions/d0f262fa-b971-4388-b6b8-893a701d247b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_ge_volume
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A H : Real)
    (hw : ∀ i, 0 < w i) (hH : 0 < H)
    (hcut : (∑ i : Fin m, w i) / H < A) :
    (A - (∑ i : Fin m, w i) / H) ^ m / ((Nat.factorial m : Nat) : Real) /
      ∏ i : Fin m, w i ≤
      ((realWeightedSimplex w (A * H)).card : Real) / H ^ m := by
  have hR : ∑ i : Fin m, w i < A * H := by
    have hmul := (div_lt_iff₀ hH).mp hcut
    nlinarith
  have hvol := weightedSimplex_card_ge_volume w (A * H) hw hR
  have hHpow : 0 < H ^ m := pow_pos hH _
  have hdiv := div_le_div_of_nonneg_right hvol (le_of_lt hHpow)
  have hbase : A - (∑ i : Fin m, w i) / H =
      (A * H - ∑ i : Fin m, w i) / H := by
    field_simp [ne_of_gt hH]
  have hscale := congrArg (fun x : Real => x ^ m) hbase
  rw [div_pow] at hscale
  calc
    (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i =
        ((A * H - ∑ i : Fin m, w i) ^ m / H ^ m) /
          ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by rw [hscale]
    _ = ((A * H - ∑ i : Fin m, w i) ^ m /
          ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) / H ^ m := by ring
    _ ≤ ((realWeightedSimplex w (A * H)).card : Real) / H ^ m := hdiv