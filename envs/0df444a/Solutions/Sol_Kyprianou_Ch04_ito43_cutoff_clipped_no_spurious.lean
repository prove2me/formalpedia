-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_clipped_no_spurious
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:06:55.918864+00:00
-- url     : https://prove2.me/submissions/e7884c79-45ae-4d52-bd0f-ab64ffe7ae86

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_short_interval_large_jump
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_clipped_cell_width
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X L : NNReal → ℝ) (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (T : NNReal) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ≤ T, ∀ k < n,
      let a := min t (T*(k:NNReal)/(n:NNReal))
      let b := min t (T*((k+1:ℕ):NNReal)/(n:NNReal))
      ρ ≤ |X b-X a| →
      ∃ s : NNReal, a < s ∧ s ≤ b ∧ ρ ≤ |X s-L s| := by
  obtain ⟨N,hN⟩ := Kyprianou.Ch04.ito43_cutoff_short_interval_large_jump
    X L hCad hLeft T ρ hρ
  filter_upwards [eventually_ge_atTop N] with n hn
  intro t ht k hk a b h
  obtain ⟨hab,hbt,hw⟩ := Kyprianou.Ch04.ito43_cutoff_clipped_cell_width T t n k
  exact hN n hn a b hab (hbt.trans ht) hw h
