-- Prove2me | solution 1 for HomeoLine.mem_connectedComponentIn_of_fixes_compl
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:41:55.034291+00:00
-- url     : https://prove2.me/submissions/c9db0609-3c8b-4da4-a417-c25c17d6f904

import Mathlib

theorem solution {h : ℝ ≃o ℝ} {U : Set ℝ}
    (hfix : ∀ y, y ∉ U → h y = y) {x : ℝ} (hx : x ∈ U) :
    h x ∈ connectedComponentIn U x := by
  -- `h` cannot push a point of `U` out of `U`
  have hmem : h x ∈ U := by
    by_contra hcon
    have h2 : h x = x := h.injective (hfix (h x) hcon)
    rw [h2] at hcon
    exact hcon hx
  -- the segment from `x` to `h x` stays in `U`
  have hseg : Set.uIcc x (h x) ⊆ U := by
    intro y hy
    by_contra hyU
    have hhy : h y = y := hfix y hyU
    rcases lt_trichotomy (h x) x with hlt | heq | hgt
    · rw [Set.uIcc_of_ge (le_of_lt hlt)] at hy
      have : h y ≤ h x := h.monotone hy.2
      rw [hhy] at this
      exact hyU (by rw [le_antisymm this hy.1]; exact hmem)
    · rw [heq, Set.uIcc_self] at hy
      exact hyU (by rw [hy]; exact hx)
    · rw [Set.uIcc_of_le (le_of_lt hgt)] at hy
      have : h x ≤ h y := h.monotone hy.1
      rw [hhy] at this
      exact hyU (by rw [le_antisymm hy.2 this]; exact hmem)
  exact (Set.ordConnected_uIcc.isPreconnected).subset_connectedComponentIn
    Set.left_mem_uIcc hseg Set.right_mem_uIcc
