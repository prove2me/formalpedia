-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_origin_drawdown_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:15:52.031602+00:00
-- url     : https://prove2.me/submissions/8e4f0f9b-4f04-4039-9fa0-4275e4ae34b9

import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source drawdown event equivalence. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (a : ℝ) (ω : Ω) (t : ℝ≥0),
      a < reflectAtSup X.X 0 t ω ↔
      X.X t ω - sSup ((fun r => X.X r ω) '' Icc 0 t) < -a := by
  intro Ω mΩ P F X a ω t
  let f : ℝ≥0 → ℝ := fun t => X.X t ω
  have hS (t : ℝ≥0) : f '' Icc 0 t =
      {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X.X u ω} := by
    ext y
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,hu.2,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,⟨bot_le,hu⟩,rfl⟩
  have hm (t : ℝ≥0) : 0 ≤ sSup (f '' Icc 0 t) := by
    apply le_csSup (levyPath_bddAbove_Icc X ω t)
    exact ⟨0,⟨le_rfl,bot_le⟩,X.X_zero ω⟩
  have he (t : ℝ≥0) : a < reflectAtSup X.X 0 t ω ↔
      f t - sSup (f '' Icc 0 t) < -a := by
    unfold reflectAtSup Kyprianou.Ch08.runningSup
    rw [← hS t,max_eq_right (hm t)]
    dsimp [f]
    constructor <;> intro h <;> linarith
  exact he t
