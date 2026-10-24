-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_monomial_tail
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:39:30.599274+00:00
-- url     : https://prove2.me/submissions/717c1ba4-8f84-4f0b-b1db-cd4987734bf4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_from_monomial_tail_73aae4b1_866b_4d65_aa9b_b11def2b6aef
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_coordinate_power_relations_73aae4b1_866b_4d65_aa9b_b11def2b6aef

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (B : ℚ)
    (hmono : ∀ (e : Fin d →₀ Nat) (t : ℚ),
      B < t → MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.monomial e (1 : ℂ)) t →
      MvPolynomial.monomial e (1 : ℂ) ∈ Ideal.span (Set.range p)) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  obtain ⟨N, hN, hpow⟩ :=
    OAI.PiExponent.FormalInterpolation.coordinate_powers_from_monomial_tail_73aae4b1_866b_4d65_aa9b_b11def2b6aef
      (w := w) hw (m := m) (p := p) B hmono
  exact
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_coordinate_power_relations_73aae4b1_866b_4d65_aa9b_b11def2b6aef
      (w := w) hw (D := D) hD (m := m) (p := p) hp N hN hpow