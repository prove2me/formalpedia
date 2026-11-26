-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ceiling_grid_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:30:54.265725+00:00
-- url     : https://prove2.me/submissions/720d8e1d-bbe1-49af-8ff4-f672f89c5680

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid
import Theorems.Thm_Kyprianou_Ch04_ito43_right_grid_limit
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Right grid approximation of a right-continuous real path converges at each time. -/
theorem solution (X : ℝ → ℝ) (T s : ℝ) (hT : 0 < T)
    (hs : s ∈ Icc 0 T) (hX : ContinuousWithinAt X (Ici s) s) :
    Tendsto (fun n : ℕ => X (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)))
      atTop (nhds (X s)) := by
  apply hX.tendsto.comp
  apply Kyprianou.Ch04.ito43_right_grid_limit T s
  intro n hn
  obtain ⟨h1,_,h2⟩ := Kyprianou.Ch04.ito43_ceiling_grid T s hT hs n hn
  exact ⟨h1,h2⟩
