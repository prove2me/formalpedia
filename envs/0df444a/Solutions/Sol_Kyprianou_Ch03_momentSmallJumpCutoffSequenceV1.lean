-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallJumpCutoffSequenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:05:11.276668+00:00
-- url     : https://prove2.me/submissions/423d3518-e85b-49c0-8913-f02e8ffb3d6a

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    :
    ∃ e : ℕ → Real, (∀ n, 0 < e n ∧ e n < 1) ∧ Tendsto e atTop (𝓝 0) := by
  refine ⟨fun n : ℕ => ((n : ℝ) + 2)⁻¹, fun n => ⟨by positivity, ?_⟩, ?_⟩
  · apply (inv_lt_one₀ (by positivity)).mpr
    linarith [show 0 ≤ (n : ℝ) by positivity]
  · apply tendsto_inv_atTop_zero.comp
    apply tendsto_atTop.mpr
    intro r
    obtain ⟨N, hN⟩ := exists_nat_ge r
    filter_upwards [eventually_ge_atTop N] with n hn
    have hh : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
