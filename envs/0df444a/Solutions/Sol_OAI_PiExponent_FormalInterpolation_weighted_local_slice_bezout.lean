-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_local_slice_bezout
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:54:11.709213+00:00
-- url     : https://prove2.me/submissions/289ce34a-834e-4e1b-b07b-5a38c09b1164
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_localized_radical_eq_prime_implies_minimalPrime
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_componentLocalLength_bound_of_minimalPrime
import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m n : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (g : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1))) (hcard : A.card = P.height)
    (hn : (n : ENat) = P.height)
    (hrad : Ideal.radical
      ((Ideal.span (Set.range g)).map
        (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (Localization.AtPrime P))) =
      P.map (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (Localization.AtPrime P)))
    (hdegree : ∀ i, logarithmicDegreeBound w H (g i))
    (hA : coordinateNormalBasisAtPrime P A)
    (M : Nat)
    (hlength : componentLocalLength (Ideal.span (Set.range g)) P = (M : ENat))
    (hpos : 0 < P.height) :
    (M : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by
  classical
  have hminimalR :=
    OAI.PiExponent.FormalInterpolation.localized_radical_eq_prime_implies_minimalPrime
      g P hrad
  let S : Finset (MvPolynomial (Fin (m + 1)) Complex) := Finset.univ.image g
  have hS : (↑S : Set (MvPolynomial (Fin (m + 1)) Complex)) = Set.range g := by
    ext f
    simp [S]
  have hI : Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex)) =
      Ideal.span (Set.range g) := congrArg Ideal.span hS
  have hminimalS :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P := by
    rw [hI]
    exact hminimalR
  have hdegreeS : ∀ f ∈ S, logarithmicDegreeBound w H f := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨i, hi, hif⟩
    rw [← hif]
    exact hdegree i
  have hlengthS : componentLocalLength
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
        (M : ENat) := by
    rw [hI]
    exact hlength
  exact OAI.PiExponent.FormalInterpolation.weighted_componentLocalLength_bound_of_minimalPrime
    w hw H hH S P hminimalS hdegreeS A hA M hlengthS