-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ClippedExitStoppingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:12:20.326429+00:00
-- url     : https://prove2.me/submissions/266883a5-269d-4b6a-bcfd-4cca7f89b9d4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
import Theorems.Thm_Kyprianou_Ch04_stateExitPreLimitBound
import Theorems.Thm_Kyprianou_Ch04_stateExitExhaustsCompactClock
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Each finite clipped spatial exit is a stopping time. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hAdapt : Adapted F X) :
    let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
      sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
    let τ (n : ℕ) (w : Ω) : NNReal :=
      (min (σ n w) (n : NNReal)).untopD (n : NNReal)
    ∀ n, IsStoppingTime F (fun w => (τ n w : WithTop NNReal)) := by
  let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
    sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
  let τ (n : ℕ) (w : Ω) : NNReal :=
    (min (σ n w) (n : NNReal)).untopD (n : NNReal)
  have hc (n : ℕ) (w : Ω) : (τ n w : WithTop NNReal) = min (σ n w) (n : NNReal) :=
    Kyprianou.Ch04.clippedClockCoe (σ n w) (n : NNReal)
  change ∀ n, IsStoppingTime F (fun w => (τ n w : WithTop NNReal))
  intro n
  have hOpen : IsOpen {x : ℝ | (n : ℝ) < |x|} :=
    isOpen_lt continuous_const continuous_abs
  have hr : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun u => X u w) (Ici t) t := by
    filter_upwards [hX.cadlag_ae] with w hw
    exact fun t => (hw t).1
  have hs : IsStoppingTime F (σ n) :=
    Kyprianou.Ch04.openHitStoppingTimeOfAE P F hRC hNull X hAdapt hr _ hOpen
  intro t
  by_cases hnt : (n : NNReal) ≤ t
  · have he : {w | (τ n w : WithTop NNReal) ≤ (t : WithTop NNReal)} = univ := by
      ext w
      simp only [mem_setOf_eq, mem_univ, iff_true]
      rw [hc]
      exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr hnt)
    rw [he]
    exact MeasurableSet.univ
  · have he : {w | (τ n w : WithTop NNReal) ≤ (t : WithTop NNReal)} =
        {w | σ n w ≤ (t : WithTop NNReal)} := by
      ext w
      simp only [mem_setOf_eq, hc, min_le_iff, WithTop.coe_le_coe, hnt, or_false]
    rw [he]
    exact hs t
