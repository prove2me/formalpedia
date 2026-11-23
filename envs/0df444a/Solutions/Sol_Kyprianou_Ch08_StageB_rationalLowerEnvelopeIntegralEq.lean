-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.rationalLowerEnvelopeIntegralEq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:12:48.946798+00:00
-- url     : https://prove2.me/submissions/0ace77c3-df46-4f93-baaf-762cbd19c410

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_rationalLowerEnvelopeAEMembershipOnSupport
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A B : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P)
    (hMono : Monotone A)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h)
    (hBMeas : ∀ y : ℝ, MeasurableSet (B y))
    (hBDef : ∀ y : ℝ, ∀ ω : Ω,
      ω ∈ B y ↔
        ∃ r : ℚ, (r : ℝ) < y ∧
          ω ∈ toMeasurable P (A (r : ℝ))) :
    ∀ y : ℝ,
      (∫ ω in B y, g ω ∂P) =
      (∫ ω in A y, g ω ∂P) := by
  have hSupp :=
    Kyprianou.Ch08.StageB.rationalLowerEnvelopeAEMembershipOnSupport
      P g A B hMeas hMono hMargin hBDef
  intro y
  have hRep : ∀ᵐ ω ∂P,
      (ω ∈ toMeasurable P (A y) ↔ ω ∈ A y) := by
    filter_upwards [(hMeas y).toMeasurable_ae_eq] with ω hω
    change (toMeasurable P (A y)) ω ↔ (A y) ω
    exact ⟨Eq.mp hω, Eq.mpr hω⟩
  have hEqInd : ∀ᵐ ω ∂P,
      (B y).indicator g ω =
        (toMeasurable P (A y)).indicator g ω := by
    filter_upwards [hSupp y, hRep] with ω hω hrω
    by_cases hg : g ω = 0
    · simp [Set.indicator, hg]
    · have hEq := hω hg
      by_cases hBy : ω ∈ B y
      · have hAy := hEq.mp hBy
        have hRy := hrω.mpr hAy
        simp [hBy, hRy]
      · have hAy : ω ∉ A y := fun h => hBy (hEq.mpr h)
        have hRy : ω ∉ toMeasurable P (A y) :=
          fun h => hAy (hrω.mp h)
        simp [hBy, hRy]
  calc
    (∫ ω in B y, g ω ∂P) =
        ∫ ω in toMeasurable P (A y), g ω ∂P := by
          rw [← integral_indicator (hBMeas y),
            ← integral_indicator (measurableSet_toMeasurable P (A y))]
          exact integral_congr_ae hEqInd
    _ = ∫ ω in A y, g ω ∂P :=
      setIntegral_congr_set (hMeas y).toMeasurable_ae_eq
