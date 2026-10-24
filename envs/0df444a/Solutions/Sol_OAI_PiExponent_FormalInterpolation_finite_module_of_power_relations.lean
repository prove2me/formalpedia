-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_module_of_power_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:31:40.015426+00:00
-- url     : https://prove2.me/submissions/34cef796-71bd-49d7-90ee-190e08993248

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomials_span_of_degree_drop
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_of_bounded_monomial_span

open scoped BigOperators

theorem solution {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous w (q j)
          ((n : ℚ) * w i - (D : ℚ))) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p))
      (MvPolynomial (Fin d) ℂ) := by
  obtain ⟨n, hn, hspan⟩ :=
    OAI.PiExponent.FormalInterpolation.monomials_span_of_degree_drop
      w hw D hD m p hrelations
  exact OAI.PiExponent.FormalInterpolation.finite_of_bounded_monomial_span
    m p n hspan