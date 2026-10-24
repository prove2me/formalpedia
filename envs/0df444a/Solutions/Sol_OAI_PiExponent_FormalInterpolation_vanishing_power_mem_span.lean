-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.vanishing_power_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:50:14.171014+00:00
-- url     : https://prove2.me/submissions/0567e642-ad6f-4a0c-a8da-ac500a6f8e04

import Mathlib

theorem solution {d m : Nat} (q : Fin m → MvPolynomial (Fin d) Complex) (f : MvPolynomial (Fin d) Complex) (hvanish : ∀ x : Fin d → Complex, (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) → MvPolynomial.eval x f = 0) : ∃ N : Nat, 0 < N ∧ f ^ N ∈ Ideal.span (Set.range q) := by
  have hmem : f ∈ MvPolynomial.vanishingIdeal ℂ
      (MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range q))) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    have := hvanish x (fun j => by
      have := hx _ (Ideal.subset_span ⟨j, rfl⟩)
      simpa [MvPolynomial.coe_aeval_eq_eval] using this)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmem
  obtain ⟨N, hN⟩ := hmem
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  rw [pow_succ]; exact Ideal.mul_mem_right _ _ hN
