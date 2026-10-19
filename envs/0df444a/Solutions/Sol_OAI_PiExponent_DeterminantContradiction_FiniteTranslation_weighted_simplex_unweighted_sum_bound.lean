-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:04:15.193664+00:00
-- url     : https://prove2.me/submissions/680ff57d-860b-470b-a9b7-d62c4668f5db

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open scoped BigOperators
open OAI.PiExponent

theorem solution
    {m : ℕ} (w : Fin m → ℝ) (H wstar : ℝ) (hwstar : 0 < wstar)
    (hw : ∀ i : Fin m, wstar ≤ w i) (a : Fin m → ℕ)
    (ha : a ∈ realWeightedSimplex w H) :
    (∑ i : Fin m, (a i : ℝ)) ≤ H / wstar := by
  classical
  unfold realWeightedSimplex at ha
  have hweighted : (∑ i : Fin m, w i * (a i : ℝ)) ≤ H :=
    (Finset.mem_filter.mp ha).2
  have hsum : wstar * (∑ i : Fin m, (a i : ℝ)) ≤ H := by
    calc
      wstar * (∑ i : Fin m, (a i : ℝ)) =
          ∑ i : Fin m, wstar * (a i : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin m, w i * (a i : ℝ) := by
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg (a i)))
      _ ≤ H := hweighted
  apply (le_div_iff₀ hwstar).2
  simpa only [mul_comm] using hsum
