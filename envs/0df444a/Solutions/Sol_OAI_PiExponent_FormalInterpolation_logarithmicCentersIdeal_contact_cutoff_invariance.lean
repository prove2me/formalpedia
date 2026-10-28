-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_contact_cutoff_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T20:49:18.529016+00:00
-- url     : https://prove2.me/submissions/59976da6-5329-486d-8632-4e609bc91b6b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_contact_cutoff_invariance
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_contact_eq_sum

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (T : Fin m → Nat)
    (hT : ∀ i, (v i.succ : Real) ≤ (T i : Real) * (v 0 : Real))
    (E : Type) [Field E] [Algebra Complex E]
    (b : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    polynomialCurveIdealContact b x (logarithmicCentersIdeal c T e) =
      polynomialCurveIdealContact b x
        (logarithmicCentersIdeal c (fun _ => e 0) e) := by
  rw [logarithmicCentersIdeal_contact_eq_sum]
  rw [logarithmicCentersIdeal_contact_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact logarithmicCenterIdeal_contact_cutoff_invariance
    (c j) v hv R e hR he hscale T hT E b x