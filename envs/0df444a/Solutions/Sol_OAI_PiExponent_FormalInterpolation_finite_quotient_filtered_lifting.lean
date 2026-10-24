-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_filtered_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:11:47.716662+00:00
-- url     : https://prove2.me/submissions/2512e5d0-e225-4dd3-8e96-67b72888a1e9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_in_span
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_power_relations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_module_of_power_relations

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  have hpow :=
    OAI.PiExponent.FormalInterpolation.coordinate_powers_in_span
      w hw D hD m p hp hquot
  have hrelations :=
    OAI.PiExponent.FormalInterpolation.homogeneous_power_relations
      w D hD m p hp hpow
  exact
    OAI.PiExponent.FormalInterpolation.finite_module_of_power_relations
      w hw D hD m p hrelations