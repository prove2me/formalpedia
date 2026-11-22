-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationPositiveNearZeroOfRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:54:08.856045+00:00
-- url     : https://prove2.me/submissions/e48fc9b2-a380-442e-933e-0b260b949ae2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hNonneg : 0 ≤ X 0 ω)
    (hRight : ContinuousWithinAt
      (fun s : ℝ≥0 => X s ω) (Set.Ici 0) 0) :
    ∃ horizon : ℝ≥0, 0 < horizon ∧
      ∀ s : ℝ≥0, 0 < s → s < horizon →
        0 < reciprocalOccupation X s ω := by
  have hSingleton : {X 0 ω} ∈ 𝓝 (X 0 ω) :=
    (isOpen_discrete ({X 0 ω} : Set ℤ)).mem_nhds (by simp)
  have hEventually : ∀ᶠ s in 𝓝[Set.Ici (0 : ℝ≥0)] (0 : ℝ≥0),
      X s ω = X 0 ω := by
    filter_upwards [hRight.eventually hSingleton] with v hv
    exact Set.mem_singleton_iff.mp hv
  have hIci : Set.Ici (0 : ℝ≥0) = Set.univ := by
    ext s
    simp
  have hEventually' : ∀ᶠ s in 𝓝 (0 : ℝ≥0),
      X s ω = X 0 ω := by
    simpa [hIci] using hEventually
  obtain ⟨eps, heps, hEq⟩ :=
    (Metric.eventually_nhds_iff).mp hEventually'
  let horizon : ℝ≥0 := ⟨eps, le_of_lt heps⟩
  have hHorizon : (0 : ℝ≥0) < horizon := heps
  refine ⟨horizon, hHorizon, ?_⟩
  intro s hs hsHorizon
  have hLocal : ∀ v : ℝ≥0, v < horizon → X v ω = X 0 ω := by
    intro v hv
    apply hEq
    have hCast : (v : ℝ) < eps := hv
    simpa [NNReal.dist_eq] using hCast
  have hIntegral :
      reciprocalOccupation X s ω =
        (ENNReal.ofReal (X 0 ω : ℝ))⁻¹ * ENNReal.ofReal (s : ℝ) := by
    unfold reciprocalOccupation
    calc
      (∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ),
        (ENNReal.ofReal (X (Real.toNNReal r) ω : ℝ))⁻¹ ∂volume) =
      (∫⁻ _r in Set.Ioc (0 : ℝ) (s : ℝ),
        (ENNReal.ofReal (X 0 ω : ℝ))⁻¹ ∂volume) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          have hrle : Real.toNNReal r ≤ s := by
            simpa only [Real.toNNReal_coe] using
              (Real.toNNReal_le_toNNReal hr.2)
          rw [hLocal (Real.toNNReal r) (lt_of_le_of_lt hrle hsHorizon)]
      _ = (ENNReal.ofReal (X 0 ω : ℝ))⁻¹ * ENNReal.ofReal (s : ℝ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
          simp
  rw [hIntegral]
  have hc : 0 < (ENNReal.ofReal (X 0 ω : ℝ))⁻¹ := by
    simp [ENNReal.inv_pos]
  have hsReal : (0 : ℝ) < (s : ℝ) := hs
  have hsENN : (0 : ENNReal) < ENNReal.ofReal (s : ℝ) :=
    ENNReal.ofReal_pos.mpr hsReal
  exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hsENN)
