-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_no_match
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:48:46.177807+00:00
-- url     : https://prove2.me/submissions/0e3f16bf-aabe-4fe9-acaa-7437ab424c07

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_zero_at_place
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (hn : ∀ j : Fin K, c j i0 ≠ a) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) = 0 := by
  classical
  have hzero : ∀ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real) = 0 := by
    intro nu
    by_cases h_aff : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
    · have :=
        OAI.PiExponent.FormalInterpolation.constant_fibre_contact_zero_at_place
          (E := E) c T e x hfibre i0 a ha hn nu h_aff
      exact_mod_cast this
    · have : polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) = 0 := by
        simp only [polynomialCurveIdealContact, if_neg h_aff]
      exact_mod_cast this
  simp_rw [hzero]
  exact finsum_zero
