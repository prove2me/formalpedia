-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_dimensional_powers_dependent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:49:23.547668+00:00
-- url     : https://prove2.me/submissions/b82fe377-f83e-46cb-906e-e3b442ed7a96

import Mathlib
open scoped BigOperators

theorem solution
    {A : Type*} [CommRing A] [Algebra ℂ A] [Module.Finite ℂ A] (x : A) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), algebraMap ℂ A (c n) * x ^ (n : Nat)) = 0 := by
  have hnot : ¬ LinearIndependent ℂ (fun n : Fin (Module.finrank ℂ A + 1) => x ^ (n : ℕ)) := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨Module.finrank ℂ A, c, ⟨i, hi⟩, ?_⟩
  simpa [Algebra.smul_def] using hc
