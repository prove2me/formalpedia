-- Prove2me | solution 1 for Kyprianou.Ch01.uniformGridCrossingInOpenIntervalPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:59:39.528005+00:00
-- url     : https://prove2.me/submissions/f2e9b452-ee21-4bd0-9bfd-d73564366537

import Mathlib.Data.Real.Basic
import Theorems.Thm_Kyprianou_Ch01_uniformGridCeilingWithinMeshPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

/-- Any interval of exceedance wider than the mesh contains a crossing grid point. -/
theorem solution
    (delta a b : ℝ) (hdelta : 0 < delta)
    (ha : 0 ≤ a) (hab : a + delta < b)
    (f : ℝ → ℝ) (x : ℝ)
    (hstrip : ∀ t, a ≤ t → t < b → x < f t) :
    ∃ n : ℕ, a ≤ (n : ℝ) * delta ∧
      (n : ℝ) * delta < b ∧ x < f ((n : ℝ) * delta) := by
  obtain ⟨n, hlo, hhi⟩ :=
    Kyprianou.Ch01.uniformGridCeilingWithinMeshPublic delta a hdelta ha
  have hb : (n : ℝ) * delta < b := lt_trans hhi hab
  exact ⟨n, hlo, hb, hstrip _ hlo hb⟩
