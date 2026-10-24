-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_relation_sum_mem_lower_weight_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:12:25.141819+00:00
-- url     : https://prove2.me/submissions/b9907816-6b39-435a-b4a8-7273eba92bd0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (n : Nat) (i : Fin d) (m : Nat)
    (p q : Fin m → MvPolynomial (Fin d) ℂ)
    (hq : ∀ j, q j ∈ Submodule.span ℂ
      {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
        (∑ k : Fin d, a k * W k) < n * W i ∧
          f = MvPolynomial.monomial a (1 : ℂ)}) :
    (∑ j, q j * p j) ∈
      Submodule.span (Algebra.adjoin ℂ (Set.range p))
        {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat,
          (∑ k : Fin d, a k * W k) < n * W i ∧
            f = MvPolynomial.monomial a (1 : ℂ)} := by
  let A := Algebra.adjoin ℂ (Set.range p)
  let S : Set (MvPolynomial (Fin d) ℂ) :=
    {f | ∃ a : Fin d →₀ Nat,
      (∑ k : Fin d, a k * W k) < n * W i ∧
        f = MvPolynomial.monomial a (1 : ℂ)}
  let M : Submodule A (MvPolynomial (Fin d) ℂ) := Submodule.span A S
  have hspan : Submodule.span ℂ S ≤ M.restrictScalars ℂ := by
    apply Submodule.span_le.mpr
    intro f hf
    exact Submodule.subset_span hf
  have hq' (j : Fin m) : q j ∈ M := hspan (hq j)
  have hterm (j : Fin m) : q j * p j ∈ M := by
    have hp : p j ∈ A := Algebra.subset_adjoin (Set.mem_range_self j)
    have hm := M.smul_mem (⟨p j, hp⟩ : A) (hq' j)
    simpa [Algebra.smul_def, mul_comm] using hm
  have hsum : (∑ j : Fin m, q j * p j) ∈ M := by
    classical
    refine Finset.induction ?_ ?_ Finset.univ
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha]
      exact M.add_mem (hterm a) ih
  simpa [A, S, M] using hsum