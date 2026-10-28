-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_centers_contact_is_single_center_of_positive_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:12:53.936223+00:00
-- url     : https://prove2.me/submissions/87fa6f6a-ee65-4514-a5cd-1723099def27

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_pairwise_comaximal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenters_contact_of_pairwise_comaximal

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E)
    (hcontact : 0 < (polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) :
    ∃ j : Fin K,
      0 < (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ∧
      (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) =
      (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) := by
  have hpair : ∀ j k : Fin K, j ≠ k →
      IsCoprime
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e)
        (logarithmicCenterIdeal (c k) (fun _ => e 0) e) :=
    logarithmicCenterIdeals_pairwise_comaximal c hc hm hK e
  exact logarithmicCenters_contact_of_pairwise_comaximal nu x
    (fun j => logarithmicCenterIdeal (c j) (fun _ => e 0) e) hpair hcontact