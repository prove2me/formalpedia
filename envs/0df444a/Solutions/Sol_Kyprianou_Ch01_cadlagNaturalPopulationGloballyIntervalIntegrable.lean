-- Prove2me | solution 1 for Kyprianou.Ch01.cadlagNaturalPopulationGloballyIntervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:53:18.050136+00:00
-- url     : https://prove2.me/submissions/3feb8ebf-dca9-4f2d-a6e3-25281a8f77dd

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch01_cadlagNaturalPopulationMeasurableAndCompactBounded
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The globally measurable, finitely bounded càdlàg population path is
Bochner-integrable on every finite real interval. -/
theorem solution
    {Ω : Type*}
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hCadlag : IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b := by
  obtain ⟨hMeas, hBounded⟩ :=
    Kyprianou.Ch01.cadlagNaturalPopulationMeasurableAndCompactBounded
      Y ω hCadlag
  intro a b
  let T : ℝ≥0 := Real.toNNReal (max a b)
  obtain ⟨M, hM0, hB⟩ := hBounded T
  have hBound : ∀ s ∈ Set.uIoc a b,
      ‖(Y (Real.toNNReal s) ω : ℝ)‖ ≤ M := by
    intro s hs
    have hs' : s ∈ Set.Ioc (min a b) (max a b) := by
      simpa only [Set.uIoc] using hs
    have hle : Real.toNNReal s ≤ T :=
      Real.toNNReal_mono hs'.2
    have hnorm : 0 ≤ (Y (Real.toNNReal s) ω : ℝ) :=
      Nat.cast_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnorm]
      using hB (Real.toNNReal s) hle
  have hFinite : volume (Set.uIoc a b) ≠ ⊤ := by
    simp
  have hBoundAE : ∀ᵐ s ∂volume.restrict (Set.uIoc a b),
      ‖(Y (Real.toNNReal s) ω : ℝ)‖ ≤ M :=
    ae_restrict_of_forall_mem (by measurability) hBound
  exact intervalIntegrable_iff.mpr
    (Measure.integrableOn_of_bounded hFinite
      hMeas.aestronglyMeasurable hBoundAE)
