-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T03:53:11.759136+00:00
-- url     : https://prove2.me/submissions/7d7eb5f0-e56e-49d5-a812-7221cdc1e239
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization_no_match
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization_matched

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
    (k : Fin m) (hk : Transcendental Complex (x k.succ)) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) = 0 ∨
    ∃ j : Fin K, c j i0 = a ∧
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
        (e k.succ : Real) *
          ∑ᶠ nu : PolynomialCurvePlace E,
            max (polynomialCurveOrder nu
              (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by
  classical
  by_cases hmatch : ∃ j : Fin K, c j i0 = a
  · rcases hmatch with ⟨j, hj⟩
    exact Or.inr ⟨j, hj,
      OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched
        c hc T e E htrdeg x hgen hfibre i0 a ha k hk j hj⟩
  · apply Or.inl
    apply OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_no_match
      c hc T e E htrdeg x hgen hfibre i0 a ha k hk
    intro j hj
    exact hmatch ⟨j, hj⟩