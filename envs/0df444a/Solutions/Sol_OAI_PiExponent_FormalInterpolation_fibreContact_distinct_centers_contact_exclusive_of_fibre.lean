-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:20:14.292487+00:00
-- url     : https://prove2.me/submissions/7d9ed58c-5746-4630-9845-e47aca784c1c

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_zero_dimensional_contact_vanishes
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_distinct_centers_contact_exclusive_of_fibre_of_coordinate_difference

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E)
    (hfibre : x 0 = 1) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
         0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by
  cases m with
  | zero =>
      exact OAI.PiExponent.FormalInterpolation.fibreContact_zero_dimensional_contact_vanishes
        c e he E nu x hfibre
  | succ m =>
      intro j k hjk
      have hdiff : ∃ i : Fin (m + 1), c j i ≠ c k i := by
        refine ⟨⟨0, Nat.zero_lt_succ m⟩, ?_⟩
        intro heq
        exact hjk (hc ⟨0, Nat.zero_lt_succ m⟩ heq)
      exact OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive_of_fibre_of_coordinate_difference
        c hc e he E nu x hfibre j k hjk hdiff
