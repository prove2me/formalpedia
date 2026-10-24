-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_lt_mem_lower_weight_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:16:55.355748+00:00
-- url     : https://prove2.me/submissions/b3be6a0b-1d81-4856-962a-9e47057f8228

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (B : Nat)
    (q : MvPolynomial (Fin d) ℂ)
    (hq : ∀ a : Fin d →₀ Nat, a ∈ q.support → (∑ k : Fin d, a k * W k) < B) :
    q ∈ Submodule.span ℂ
      {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
        (∑ k : Fin d, a k * W k) < B ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
  classical
  rw [MvPolynomial.as_sum q]
  apply Submodule.sum_mem
  intro a ha
  have hdeg := hq a ha
  have hgen : MvPolynomial.monomial a (1 : ℂ) ∈
      {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
        (∑ k : Fin d, a k * W k) < B ∧ f = MvPolynomial.monomial a (1 : ℂ)} :=
    ⟨a, hdeg, rfl⟩
  have hsmul : (MvPolynomial.coeff a q) • MvPolynomial.monomial a (1 : ℂ) =
      MvPolynomial.monomial a (MvPolynomial.coeff a q) := by
    rw [MvPolynomial.smul_monomial]
    simp
  rw [← hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hgen)