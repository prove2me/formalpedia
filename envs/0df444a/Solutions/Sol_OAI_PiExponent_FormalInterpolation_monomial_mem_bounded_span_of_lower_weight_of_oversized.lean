-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight_of_oversized
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:20:23.585464+00:00
-- url     : https://prove2.me/submissions/fbc0755d-9e22-40a4-8b4e-1d50374d3293

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mem_bounded_span_of_lower_weight_step
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (W : Fin d → Nat) (hW : ∀ i, 0 < W i)
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (hred : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈
        Submodule.span A
          {f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat,
              (∑ k : Fin d, a k * W k) < n i * W i ∧
                f = MvPolynomial.monomial a (1 : ℂ)})
    (e : Fin d →₀ Nat) (hover : ∃ i : Fin d, n i ≤ e i)
    (hbelow : ∀ b : Fin d →₀ Nat,
      (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) →
        MvPolynomial.monomial b (1 : ℂ) ∈
          Submodule.span A
            {f : MvPolynomial (Fin d) ℂ |
              ∃ a : Fin d →₀ Nat,
                (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)}):
    MvPolynomial.monomial e (1 : ℂ) ∈
      Submodule.span A
        {f : MvPolynomial (Fin d) ℂ |
          ∃ a : Fin d →₀ Nat,
            (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
  have hstep :=
    OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight_step
      A W n hred e hover
  have hle :
      Submodule.span A
          ({f : MvPolynomial (Fin d) ℂ |
              ∃ a : Fin d →₀ Nat,
                (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} ∪
            {f : MvPolynomial (Fin d) ℂ |
              ∃ b : Fin d →₀ Nat,
                (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) ∧
                  f = MvPolynomial.monomial b (1 : ℂ)}) ≤
        Submodule.span A
          {f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat,
              (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
    apply Submodule.span_le.2
    intro f hf
    change
      f ∈ {g : MvPolynomial (Fin d) ℂ |
        ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧
          g = MvPolynomial.monomial a (1 : ℂ)} ∨
      f ∈ {g : MvPolynomial (Fin d) ℂ |
        ∃ b : Fin d →₀ Nat,
          (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) ∧
            g = MvPolynomial.monomial b (1 : ℂ)} at hf
    rcases hf with hbounded | hlower
    · exact Submodule.subset_span hbounded
    · rcases hlower with ⟨b, hlt, rfl⟩
      exact hbelow b hlt
  exact hle hstep