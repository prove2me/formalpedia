-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.choose_monic_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:33:20.674994+00:00
-- url     : https://prove2.me/submissions/c319be23-8961-4fac-a51d-b0739d77fe98

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_exists_bounded_fintype_sum

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι]
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (u : ι →₀ ℕ) (s : ℕ)
    (hu : s ≤ ∑ i, u i / b i) :
    ∃ k : ι → ℕ, (∀ i, k i * b i ≤ u i) ∧ (∑ i, k i = s) := by
  let q : ι → ℕ := fun i => u i / b i
  have hq : s ≤ ∑ i, q i := by
    simpa [q] using hu
  obtain ⟨k, hk, hks⟩ :=
    OAI.PiExponent.WeightedDivision.exists_bounded_fintype_sum q s hq
  refine ⟨k, ?_, hks⟩
  intro i
  calc
    k i * b i ≤ q i * b i := Nat.mul_le_mul_right _ (hk i)
    _ ≤ u i := Nat.div_mul_le_self (u i) (b i)