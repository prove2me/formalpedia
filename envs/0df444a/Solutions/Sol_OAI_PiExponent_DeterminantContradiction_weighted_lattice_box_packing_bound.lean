-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:01:11.884968+00:00
-- url     : https://prove2.me/submissions/50f4fa56-d9ab-416c-95c3-e224320e5123

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_volume_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume

open scoped BigOperators

theorem solution
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T)
    (hs : ∀ a ∈ s, ∑ i : Fin m, w i * (a i : ℝ) ≤ T) :
    (s.card : ℝ) ≤
      (T + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by
  let U : ℝ := T + ∑ i : Fin m, w i
  have hsum : 0 ≤ ∑ i : Fin m, w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (hw i)
  have hU : 0 ≤ U := by
    dsimp [U]
    exact add_nonneg hT hsum
  have hpack :=
    OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_volume_bound
      m s w T hw hT hs
  have hvol :=
    OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume m U hU
  change (s.card : ℝ) ≤ U ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i)
  have hpack' :
      ((s.card : ℝ) * ∏ i : Fin m, w i) ≤ U ^ m / (Nat.factorial m : ℝ) := by
    simpa [U, hvol] using hpack
  have hfac : 0 < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hprod : 0 < ∏ i : Fin m, w i := by
    apply Finset.prod_pos
    intro i hi
    exact hw i
  have hquot :
      (s.card : ℝ) ≤ (U ^ m / (Nat.factorial m : ℝ)) / ∏ i : Fin m, w i := by
    exact (le_div_iff₀ hprod).2 hpack'
  calc
    (s.card : ℝ) ≤ (U ^ m / (Nat.factorial m : ℝ)) / ∏ i : Fin m, w i := hquot
    _ = U ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by rw [div_div]