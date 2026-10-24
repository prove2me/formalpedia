-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_powers_in_finite_homogeneous_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:41:06.082706+00:00
-- url     : https://prove2.me/submissions/c455a6f5-7eb9-4ad2-8f8e-cb57e3a61996

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_coordinate_relation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_relation_gives_coordinate_power

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ Ideal.span (Set.range p) := by
  intro i
  obtain ⟨q, hq, hqI⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_relation
      (m := m) (p := p) hquot i
  exact OAI.PiExponent.FormalInterpolation.weighted_relation_gives_coordinate_power
    w hw D hD (m := m) p hp i q hq hqI