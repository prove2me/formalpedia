-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CompactHalfplaneBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:30:38.973725+00:00
-- url     : https://prove2.me/submissions/9da6a140-9806-43d7-807e-f5244d790306

import Mathlib
open Set
set_option autoImplicit false

/-- A continuous function supported on a compact rectangle is bounded on the positive half-plane. -/
theorem solution (g : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hz : ∀ s x, 0 ≤ s → (R < s ∨ R < |x|) → g s x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ s x, 0 ≤ s → |g s x| ≤ K := by
  have hsub : Icc (0 : ℝ) R ×ˢ Icc (-R) R ⊆ Ici (0 : ℝ) ×ˢ univ :=
    fun z hz => ⟨hz.1.1,mem_univ _⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.mono hsub)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro s x hs
  by_cases h : R < s ∨ R < |x|
  · rw [hz s x hs h,abs_zero]
    exact zero_le_one.trans (le_max_right _ _)
  · push Not at h
    exact (show |g s x| ≤ C by
      simpa [Real.norm_eq_abs] using hC (s,x) ⟨⟨hs,h.1⟩,abs_le.mp h.2⟩).trans
      (le_max_left _ _)
