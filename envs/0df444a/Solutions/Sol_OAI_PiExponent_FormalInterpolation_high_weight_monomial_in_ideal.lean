-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.high_weight_monomial_in_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:58:29.02567+00:00
-- url     : https://prove2.me/submissions/f9bb642c-c232-4f7e-b5c3-453e3a48bda7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weight_le_cutoff_of_lt

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hpow : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ I)
    (t : ℚ) (e : Fin d →₀ Nat) (c : ℂ)
    (hweight : (∑ i : Fin d, ((n i : ℚ) - 1) * w i) < Finsupp.weight w e) :
    MvPolynomial.monomial e c ∈ I := by
  have hlarge : ∃ i : Fin d, n i ≤ e i := by
    by_contra h
    have hlt : ∀ i : Fin d, e i < n i := by
      intro i
      have hi : ¬ n i ≤ e i := by
        intro hle
        exact h ⟨i, hle⟩
      omega
    have hb := OAI.PiExponent.FormalInterpolation.weight_le_cutoff_of_lt
      w hw n hn e hlt
    exact (not_lt_of_ge hb) hweight
  obtain ⟨i, hi⟩ := hlarge
  let r : Fin d →₀ Nat := e - Finsupp.single i (n i)
  have hdecomp : Finsupp.single i (n i) + r = e := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [r, Nat.sub_add_cancel hi] <;> omega
    · simp [r, hji]
  rw [← hdecomp, MvPolynomial.monomial_single_add]
  simpa [mul_comm] using I.mul_mem_left (MvPolynomial.monomial r c) (hpow i)
