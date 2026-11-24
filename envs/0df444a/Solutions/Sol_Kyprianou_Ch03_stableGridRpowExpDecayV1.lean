-- Prove2me | solution 1 for Kyprianou.Ch03.stableGridRpowExpDecayV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:45:22.222364+00:00
-- url     : https://prove2.me/submissions/6d490961-ebf9-4996-8187-d8bd9b3e01ec

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
theorem solution (α c : ℝ) (hα : 1 < α) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * ((n : ℝ) + 1) ^ (1 - 1 / α))) atTop (𝓝 0) := by
  have hp : 0 < 1 - 1 / α := by
    have ha : 0 < α := by linarith
    have h := (div_lt_iff₀ ha).mpr (show (1 : ℝ) < 1 * α by simpa using hα)
    linarith
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n h
    have hh : (N : ℝ) ≤ n := by exact_mod_cast h
    linarith
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (1 - 1 / α)) atTop atTop :=
    (tendsto_rpow_atTop hp).comp hn
  have he : Tendsto (fun n : ℕ => -c * ((n : ℝ) + 1) ^ (1 - 1 / α)) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp hr) (-b / c)] with n hn
    have hh := (div_le_iff₀ hc).mp hn
    nlinarith
  exact Real.tendsto_exp_atBot.comp he
