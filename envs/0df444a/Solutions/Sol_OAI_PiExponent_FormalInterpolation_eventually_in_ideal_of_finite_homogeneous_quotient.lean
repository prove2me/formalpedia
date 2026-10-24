-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventually_in_ideal_of_finite_homogeneous_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:29:25.766296+00:00
-- url     : https://prove2.me/submissions/d2799e40-b50d-453f-8760-fcdd59fa9795

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_in_finite_homogeneous_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_high_weight_terms_in_coordinate_power_ideal

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) :
    ∃ B : ℚ, ∀ (t : ℚ) (f : MvPolynomial (Fin d) ℂ),
      B < t → MvPolynomial.IsWeightedHomogeneous w f t →
        f ∈ Ideal.span (Set.range p) := by
  classical
  let I : Ideal (MvPolynomial (Fin d) ℂ) := Ideal.span (Set.range p)
  have hcoord :=
    OAI.PiExponent.FormalInterpolation.coordinate_powers_in_finite_homogeneous_ideal
      w hw D hD m p hp hquot
  let n : Fin d → Nat := fun i => Classical.choose (hcoord i)
  have hn : ∀ i, 0 < n i := by
    intro i
    exact (Classical.choose_spec (hcoord i)).1
  have hpow : ∀ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ I := by
    intro i
    exact (Classical.choose_spec (hcoord i)).2
  let B : ℚ := ∑ i : Fin d, ((n i : ℚ) - 1) * w i
  refine ⟨B, ?_⟩
  intro t f hBt hf
  have hhigh :=
    OAI.PiExponent.FormalInterpolation.high_weight_terms_in_coordinate_power_ideal
      (d := d) w hw n hn I hpow
  apply hhigh t f
  · simpa [B] using hBt
  · exact hf
