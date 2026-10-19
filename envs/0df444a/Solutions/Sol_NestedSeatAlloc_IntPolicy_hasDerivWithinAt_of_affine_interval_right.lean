-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.hasDerivWithinAt_of_affine_interval_right
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-19T12:23:57.211811+00:00
-- url     : https://prove2.me/submissions/9b4437d1-c00f-4912-b3b4-156bb66d0c4a

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ {g : ℝ → ℝ} {m : ℕ} {c d s : ℝ}
    (_hs : s ∈ Set.Icc (m : ℝ) (m + 1))
    (_haff : ∀ t ∈ Set.Icc (m : ℝ) (m + 1), g t = c + d * t),
    HasDerivWithinAt g d (Set.Ici s) s) := by
  intro h
  have hs : (1 : ℝ) ∈ Set.Icc (((0 : ℕ) : ℝ)) (((0 : ℕ) : ℝ) + 1) := by
    simp
  have haff : ∀ t ∈ Set.Icc (((0 : ℕ) : ℝ)) (((0 : ℕ) : ℝ) + 1),
      (fun t : ℝ => if t ≤ 1 then (0 : ℝ) else 1) t = (0 : ℝ) + (0 : ℝ) * t := by
    intro t ht
    have : t ≤ 1 := by simpa using ht.2
    simp [this]
  have hd := h (g := fun t : ℝ => if t ≤ 1 then (0 : ℝ) else 1) (m := 0) (c := 0) (d := 0) (s := 1) hs haff
  have hc := hd.continuousWithinAt
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (1/2) (by norm_num)
  have h1 : (1 + δ / 2 : ℝ) ∈ Set.Ici (1 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  have h2 : dist (1 + δ / 2 : ℝ) 1 < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have := hδ' h1 h2
  have hn : ¬ (1 + δ / 2 : ℝ) ≤ 1 := by linarith
  simp [hn, Real.dist_eq] at this
  norm_num at this
