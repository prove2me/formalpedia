-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_critical_representatives_of_numerics
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:49:05.824127+00:00
-- url     : https://prove2.me/submissions/fff70255-3000-42de-adbe-972dab6d8454
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_eventual_subcritical_representatives_of_numerics
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
          P - Q ∈ (logarithmicCentersIdeal c (fun _ => e 0) e) ^ n ∧
          ∀ a ∈ Q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * (R : Real) := by
  obtain ⟨δ, hδpos, hδR, n0, hrep⟩ :=
    OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_subcritical_representatives_of_numerics
      c hc w v sigma hnum R e hR he hscale
  refine ⟨n0, ?_⟩
  intro n hn P
  obtain ⟨Q, hmem, hweight⟩ := hrep n hn P
  refine ⟨Q, hmem, ?_⟩
  intro a ha
  calc
    ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * δ := hweight a ha
    _ ≤ (n : Real) * (R : Real) :=
      mul_le_mul_of_nonneg_left hδR.le (Nat.cast_nonneg n)