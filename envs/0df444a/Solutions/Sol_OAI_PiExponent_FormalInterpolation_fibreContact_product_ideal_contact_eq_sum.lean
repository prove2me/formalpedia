-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_product_ideal_contact_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:14:35.787388+00:00
-- url     : https://prove2.me/submissions/0797447e-d725-4a04-a41c-a7ed15eceef5

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveIdealContact_finset_product_of_pairwise_eq_or_comaximal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_eq_or_comaximal

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) =
      ∑ j : Fin K, polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) := by
  classical
  unfold logarithmicCentersIdeal
  apply polynomialCurveIdealContact_finset_product_of_pairwise_eq_or_comaximal
  intro i hi j hj hij
  rcases logarithmicCenterIdeal_eq_or_comaximal
      (c i) (c j) (fun _ => e 0) e with heq | htop
  · exact Or.inl heq
  · exact Or.inr htop