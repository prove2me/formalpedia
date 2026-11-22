-- Prove2me | solution 1 for Kyprianou.Ch01.rightNaturalStoppingMinTimeFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:31:23.252049+00:00
-- url     : https://prove2.me/submissions/7c74f7ae-1228-4317-8ec9-c551ca75b8bf

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Clip an arbitrary right-natural stopping time at a finite horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight Y t)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime Y tau)
    (n : ℝ≥0) :
    let T : Ω → ℝ≥0 :=
      fun ω => (min (tau ω) (n : WithTop ℝ≥0)).untopD n
    (∀ ω, ((T ω : ℝ≥0) : WithTop ℝ≥0) =
      min (tau ω) (n : WithTop ℝ≥0)) ∧
    IsStoppingTime F (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) ∧
    (∀ ω, T ω ≤ n) := by
  dsimp only
  let rho : Ω → WithTop ℝ≥0 :=
    fun ω => min (tau ω) (n : WithTop ℝ≥0)
  let T : Ω → ℝ≥0 := fun ω => (rho ω).untopD n
  have hStop : IsStoppingTime F tau := by
    intro t
    change MeasurableSet[F t] {ω : Ω | tau ω ≤ (t : WithTop ℝ≥0)}
    rw [hF t]
    exact hTau t
  have hRhoStop : IsStoppingTime F rho :=
    hStop.min_const n
  have hRhoFinite (ω : Ω) : rho ω ≠ ⊤ := by
    intro heq
    have hle : rho ω ≤ (n : WithTop ℝ≥0) :=
      min_le_right _ _
    rw [heq] at hle
    exact (not_le_of_gt (WithTop.coe_lt_top n)) hle
  have hTeq (ω : Ω) :
      ((T ω : ℝ≥0) : WithTop ℝ≥0) = rho ω := by
    cases hr : rho ω with
    | top => exact (hRhoFinite ω hr).elim
    | coe t =>
        simpa only [T, hr] using
          congrArg (fun u : ℝ≥0 => (u : WithTop ℝ≥0))
            (WithTop.untopD_coe n t)
  have heqFun :
      (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) = rho :=
    funext hTeq
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    exact hTeq ω
  · rw [heqFun]
    exact hRhoStop
  · intro ω
    have hle : rho ω ≤ (n : WithTop ℝ≥0) :=
      min_le_right _ _
    rw [← hTeq ω] at hle
    exact WithTop.coe_le_coe.mp hle
