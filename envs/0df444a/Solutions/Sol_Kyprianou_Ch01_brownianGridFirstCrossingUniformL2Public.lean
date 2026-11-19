-- Prove2me | solution 1 for Kyprianou.Ch01.brownianGridFirstCrossingUniformL2Public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:15:36.222243+00:00
-- url     : https://prove2.me/submissions/2411c6d9-b2f0-46f3-84cf-3971f3975e43

import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalGridFirstCrossingMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_brownianGridStoppedL2BoundPublic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The first-crossing grid martingales have a common second moment bound at fixed T. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma q s : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    let delta : ℝ≥0 := T / (N : ℝ≥0)
    let tau : Ω → ℕ := fun ω => by
      classical
      exact Nat.find (show ∃ k : ℕ,
        k = N ∨ s < X ((k : ℝ≥0) * delta) ω from ⟨N, Or.inl rfl⟩)
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let M : Ω → ℝ := fun ω =>
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    Integrable (fun ω => M ω ^ 2) P ∧
      (∫ ω, M ω ^ 2 ∂P) ≤
        Real.exp (sigma ^ 2 * theta ^ 2 * (T : ℝ)) := by
  let delta : ℝ≥0 := T / (N : ℝ≥0)
  let tau : Ω → ℕ := fun ω => by
    classical
    exact Nat.find (show ∃ k : ℕ,
      k = N ∨ s < X ((k : ℝ≥0) * delta) ω from ⟨N, Or.inl rfl⟩)
  obtain ⟨hBound, hStop⟩ :=
    naturalGridFirstCrossingMeasurablePublic X s delta N
  obtain ⟨hint, hmean⟩ :=
    brownianGridStoppedL2BoundPublic
      P X sigma gamma q hsigma hq hX hMeas
      delta tau N hBound hStop
  have hnzero : (N : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hgrid : (N : ℝ≥0) * delta = T := by
    dsimp [delta]
    field_simp
  have hgridReal : (((N : ℝ≥0) * delta) : ℝ) = (T : ℝ) :=
    congrArg (fun z : ℝ≥0 => (z : ℝ)) hgrid
  rw [hgridReal] at hmean
  exact ⟨hint, hmean⟩
