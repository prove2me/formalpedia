-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.integer_weighted_monomials_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:55:36.197784+00:00
-- url     : https://prove2.me/submissions/1660de4f-b7aa-4d8c-92b1-79fa02692b44

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_has_lower_weight_span
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomials_span_of_lower_weight_bounds

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (hW : ∀ i, 0 < W i)
    (delta : Nat) (hdelta : 0 < delta) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧
        ∀ j, ∀ a : Fin d →₀ Nat, a ∈ (q j).support →
          (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) =
            (n : ℤ) * (W i : ℤ) - (delta : ℤ)) :
    ∃ n : Fin d → Nat, (∀ i, 0 < n i) ∧
      ∀ e : Fin d →₀ Nat,
        MvPolynomial.monomial e (1 : ℂ) ∈
          Submodule.span (Algebra.adjoin ℂ (Set.range p))
            {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
              (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
  classical
  have hlow :=
    OAI.PiExponent.FormalInterpolation.coordinate_power_has_lower_weight_span
      W hW delta hdelta m p hrelations
  let n : Fin d → Nat := fun i => Classical.choose (hlow i)
  have hn : ∀ i, 0 < n i := by
    intro i
    exact (Classical.choose_spec (hlow i)).1
  have hred : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈
        Submodule.span (Algebra.adjoin ℂ (Set.range p))
          {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
            (∑ k : Fin d, a k * W k) < n i * W i ∧
              f = MvPolynomial.monomial a (1 : ℂ)} := by
    intro i
    have hpow := (Classical.choose_spec (hlow i)).2
    simpa [n] using hpow
  refine ⟨n, hn, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.monomials_span_of_lower_weight_bounds
    (Algebra.adjoin ℂ (Set.range p)) W hW n hn hred
