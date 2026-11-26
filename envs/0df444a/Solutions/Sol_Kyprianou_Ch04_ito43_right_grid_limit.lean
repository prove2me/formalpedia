-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_right_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:19:41.681443+00:00
-- url     : https://prove2.me/submissions/a147fe85-7d4c-4622-a0c9-df2e45ebbff9

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Any grid approximation between the original time and one vanishing mesh to its right
converges through the right-neighbourhood filter. -/
theorem solution (T s : ℝ) (r : ℕ → ℝ)
    (h : ∀ n : ℕ, 0 < n → s ≤ r n ∧ r n ≤ s + T / (n : ℝ)) :
    Tendsto r atTop (nhdsWithin s (Ici s)) := by
  have hpos := eventually_gt_atTop (0 : ℕ)
  have hlo : ∀ᶠ n in atTop, s ≤ r n := hpos.mono fun n hn => (h n hn).1
  have hhi : ∀ᶠ n in atTop, r n ≤ s + T / (n : ℝ) :=
    hpos.mono fun n hn => (h n hn).2
  have hlim : Tendsto (fun n : ℕ => s + T / (n : ℝ)) atTop (nhds s) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat T)
  exact tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlo hhi, hlo⟩
