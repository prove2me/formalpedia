-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_mul_lower_weight_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:51:38.859665+00:00
-- url     : https://prove2.me/submissions/6629982e-2e13-481e-a971-e76793c61f35

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat}
    (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (W : Fin d → Nat) (c : Fin d →₀ Nat) (L : Nat)
    (p : MvPolynomial (Fin d) ℂ)
    (hp : p ∈ Submodule.span A
      {f : MvPolynomial (Fin d) ℂ |
        ∃ a : Fin d →₀ Nat,
          (∑ k : Fin d, a k * W k) < L ∧
            f = MvPolynomial.monomial a (1 : ℂ)}) :
    MvPolynomial.monomial c (1 : ℂ) * p ∈ Submodule.span A
      {f : MvPolynomial (Fin d) ℂ |
        ∃ b : Fin d →₀ Nat,
          (∑ k : Fin d, b k * W k) <
              (∑ k : Fin d, c k * W k) + L ∧
            f = MvPolynomial.monomial b (1 : ℂ)} := by
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.monomial c (1 : ℂ) * q ∈ Submodule.span A
        {f : MvPolynomial (Fin d) ℂ |
          ∃ b : Fin d →₀ Nat,
            (∑ k : Fin d, b k * W k) <
                (∑ k : Fin d, c k * W k) + L ∧
              f = MvPolynomial.monomial b (1 : ℂ)})
    ?_ ?_ ?_ ?_ hp
  · rintro f ⟨a, ha, rfl⟩
    apply Submodule.subset_span
    refine ⟨c + a, ?_, ?_⟩
    · have hsum :
          (∑ k : Fin d, (c + a) k * W k) =
            (∑ k : Fin d, c k * W k) +
              (∑ k : Fin d, a k * W k) := by
        simp [add_mul, Finset.sum_add_distrib]
      rw [hsum]
      exact Nat.add_lt_add_left ha _
    · rw [MvPolynomial.monomial_mul]
      simp
  · simp
  · intro x y hx hy hxP hyP
    rw [mul_add]
    exact Submodule.add_mem _ hxP hyP
  · intro r x hx ih
    have heq :
        MvPolynomial.monomial c (1 : ℂ) * (r • x) =
          r • (MvPolynomial.monomial c (1 : ℂ) * x) := by
      simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    rw [heq]
    exact Submodule.smul_mem _ r ih