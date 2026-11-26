-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41GridRestartFactorV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:48:29.59304+00:00
-- url     : https://prove2.me/submissions/7a8947cc-57ce-4eac-9b61-6a60a9e17fca

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstStoppingV2
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteSlopeCylinderV2
import Theorems.Thm_Kyprianou_Ch04_exercise41StoppedEventFactorV2
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

/-- Each finite grid hit has a measurable successful restart event with
probability bounded below by the uniform slope-window probability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (D R : Finset NNReal) (b δ : NNReal) (e : ℝ)
    (hD : ∀ t ∈ D, t ≤ b)
    (hR : ∀ u ∈ R, 0 < u ∧ u ≤ δ) :
    let C : NNReal → Set Ω := fun t => {ω | |L.X t ω| < e}
    let τ := exercise41GridFirstV2 D C b
    let A : Set Ω := {ω | ∃ t ∈ D, ω ∈ C t}
    let G : Set (NNReal → ℝ) :=
      {y | ∀ u ∈ R, L.drift / 2 * (u : ℝ) ≤ y u}
    let B := A ∩ {ω | (fun u => L.X (τ ω + u) ω - L.X (τ ω) ω) ∈ G}
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    MeasurableSet A ∧ MeasurableSet B ∧ p * P A ≤ P B := by
  dsimp only
  let C : NNReal → Set Ω := fun t => {ω | |L.X t ω| < e}
  let τ := exercise41GridFirstV2 D C b
  let A : Set Ω := {ω | ∃ t ∈ D, ω ∈ C t}
  let G : Set (NNReal → ℝ) :=
    {y | ∀ u ∈ R, L.drift / 2 * (u : ℝ) ≤ y u}
  have hc (t : NNReal) : MeasurableSet[F t] (C t) := by
    have hr : MeasurableSet {x : ℝ | |x| < e} :=
      (isOpen_lt continuous_abs continuous_const).measurableSet
    exact (L.adapted t) hr
  obtain ⟨ht, ha⟩ := exercise41GridFirstStoppingV2 F D C b hD hc
  obtain ⟨hg, hp⟩ := exercise41FiniteSlopeCylinderV2 P F L δ R hR
  have hstop := isStoppingTime_withTop_of_le_events τ ht
  have ham : MeasurableSet A := stoppedHistory_event_measurable τ A ha
  have hym := levy_finiteStopping_stoppedFuturePath_measurable L τ hstop
  refine ⟨ham, ham.inter (hym hg), ?_⟩
  have hfac := exercise41StoppedEventFactorV2 P F L τ ht A ha G hg
  change _ ≤ P (A ∩ {ω | (fun u =>
    L.X (τ ω + u) ω - L.X (τ ω) ω) ∈ G})
  rw [hfac]
  calc
    _ ≤ P {ω | (fun u => L.X u ω) ∈ G} * P A := by
      gcongr <;> exact hp
    _ = _ := mul_comm _ _
