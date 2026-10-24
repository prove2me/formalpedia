-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:22:36.153686+00:00
-- url     : https://prove2.me/submissions/085bea82-8605-45fb-996b-134d08577c44

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventually_in_ideal_of_finite_homogeneous_quotient
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_quotient_of_homogeneous_tail

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  obtain ⟨B, hB⟩ :=
    OAI.PiExponent.FormalInterpolation.eventually_in_ideal_of_finite_homogeneous_quotient
      w hw D hD m p hp hquot
  exact
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_quotient_of_homogeneous_tail
      w hw D hD m p hp B hB