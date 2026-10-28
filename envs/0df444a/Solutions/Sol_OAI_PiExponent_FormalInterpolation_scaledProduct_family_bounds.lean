-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaledProduct_family_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T18:18:10.025722+00:00
-- url     : https://prove2.me/submissions/fc25ea2d-46fa-49c4-a2f8-ad5003cece54

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_mem_ideal_power
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_finite_product

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s : Nat) (hs : 0 < s) (D : Real)
    (k n N : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (eFin : Fin N ≃ (Fin k → Fin n)) :
    (∀ j : Fin N, (∏ t : Fin k, f (eFin j t)) ∈ I ^ (k * s)) ∧
    (∀ j : Fin N, ∀ a ∈ (∏ t : Fin k, f (eFin j t)).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ (k : Real) * D) := by
  constructor
  · intro j
    simpa using
      OAI.PiExponent.FormalInterpolation.scaledProduct_mem_ideal_power
        (I := I) (s := s) (f := fun t => f (eFin j t))
        (by
          intro t
          exact hf (eFin j t))
  · intro j a ha
    have h :=
      OAI.PiExponent.FormalInterpolation.weighted_support_finite_product
        (w := w) (f := fun t => f (eFin j t)) (B := fun _ => D)
        (by
          intro t b hb
          exact hweight (eFin j t) b hb)
    simpa using h a ha