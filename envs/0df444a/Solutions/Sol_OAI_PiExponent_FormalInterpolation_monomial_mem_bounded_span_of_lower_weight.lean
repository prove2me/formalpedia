-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:10:44.750744+00:00
-- url     : https://prove2.me/submissions/0b6c2230-9f6f-45d2-8d13-486cfb9c6e25

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mem_bounded_span_of_lower_weight_of_oversized

open scoped BigOperators

theorem solution
    {d : Nat}
    (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (W : Fin d → Nat)
    (hW : ∀ i, 0 < W i)
    (n : Fin d → Nat)
    (hn : ∀ i, 0 < n i)
    (hred : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈
        Submodule.span A
          {f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat,
              (∑ k : Fin d, a k * W k) < n i * W i ∧
              f = MvPolynomial.monomial a (1 : ℂ)})
    (e : Fin d →₀ Nat)
    (hbelow : ∀ b : Fin d →₀ Nat,
      (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) →
        MvPolynomial.monomial b (1 : ℂ) ∈
          Submodule.span A
            {f : MvPolynomial (Fin d) ℂ |
              ∃ a : Fin d →₀ Nat,
                (∀ i, a i < n i) ∧
                f = MvPolynomial.monomial a (1 : ℂ)}) :
    MvPolynomial.monomial e (1 : ℂ) ∈
      Submodule.span A
        {f : MvPolynomial (Fin d) ℂ |
          ∃ a : Fin d →₀ Nat,
            (∀ i, a i < n i) ∧
            f = MvPolynomial.monomial a (1 : ℂ)} := by
  classical
  let wt : (Fin d →₀ Nat) → Nat := fun b => ∑ k : Fin d, b k * W k
  have hrec : ∀ m : Nat, ∀ b : Fin d →₀ Nat, wt b = m →
      MvPolynomial.monomial b (1 : ℂ) ∈
        Submodule.span A
          {f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat,
              (∀ i, a i < n i) ∧
              f = MvPolynomial.monomial a (1 : ℂ)} := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro b hwt
        by_cases hb : ∀ i : Fin d, b i < n i
        · exact Submodule.subset_span ⟨b, hb, rfl⟩
        · have hover : ∃ i : Fin d, n i ≤ b i := by
            by_contra h
            push_neg at h
            exact hb (fun i => h i)
          apply OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight_of_oversized
            (A := A) (W := W) (hW := hW) (n := n) (hn := hn)
            (hred := hred) (e := b) hover
          intro c hc
          exact ih (wt c) (by
            rw [← hwt]
            simpa [wt] using hc) c rfl
  exact hrec (wt e) e rfl