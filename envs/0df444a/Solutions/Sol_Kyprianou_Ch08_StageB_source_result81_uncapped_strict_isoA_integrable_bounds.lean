-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_uncapped_strict_isoA_integrable_bounds
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T16:49:13.692803+00:00
-- url     : https://prove2.me/submissions/4c575547-cd85-41b8-add9-4a7db04504f9

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_real_avram_stopped_reward_integrable
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weightR := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoffR := fun ω => if U ω < L ω then discount (U ω).toNNReal * reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω) else 0
    let rewR := fun ω => reward (fun s => X.X s ω)
    (Integrable weightR P ∧ ∀ ω, 0 ≤ weightR ω ∧ weightR ω ≤ 1) ∧
    (Integrable payoffR P ∧ ∀ ω, 0 ≤ payoffR ω ∧ payoffR ω ≤ 1) ∧
    (Integrable rewR P ∧ ∀ ω, 0 ≤ rewR ω ∧ rewR ω ≤ 1) := by
  intro U L weightR payoffR rewR
  obtain ⟨hPayoff, hWeight, hReward⟩ :=
    Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward_integrable
      X lower upper discount hd hdb reward hr hrb
  refine ⟨⟨hWeight, ?_⟩, ⟨hPayoff, ?_⟩, ⟨hReward, fun ω => hrb _⟩⟩
  · intro ω
    dsimp [weightR]
    split
    · exact hdb _
    · exact ⟨le_rfl, zero_le_one⟩
  · intro ω
    dsimp [payoffR]
    split
    · exact ⟨mul_nonneg (hdb _).1 (hrb _).1,
        mul_le_one₀ (hdb _).2 (hrb _).1 (hrb _).2⟩
    · exact ⟨le_rfl, zero_le_one⟩
