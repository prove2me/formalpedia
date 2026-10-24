-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:53:44.57662+00:00
-- url     : https://prove2.me/submissions/0b4c0396-eb6b-4558-8c7e-07bb2f342ef9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_pairwise_sup_eq_top
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveIdealContact_sup_eq_top_exclusive

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
         0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by
  intro j k hjk
  exact polynomialCurveIdealContact_sup_eq_top_exclusive nu x
    (logarithmicCenterIdeal (c j) (fun _ => e 0) e)
    (logarithmicCenterIdeal (c k) (fun _ => e 0) e)
    (logarithmicCenterIdeal_pairwise_sup_eq_top c hc e he j k hjk)
