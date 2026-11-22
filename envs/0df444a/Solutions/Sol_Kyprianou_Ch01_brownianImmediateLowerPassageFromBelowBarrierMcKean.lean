-- Prove2me | solution 1 for Kyprianou.Ch01.brownianImmediateLowerPassageFromBelowBarrierMcKean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:29:47.913817+00:00
-- url     : https://prove2.me/submissions/a794260b-56e8-43a1-9c21-8360a218ff89

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierPassageAeZero
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassageEqShiftedNegUpperPublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma x barrier : ℝ)
    (hsigma : 0 < sigma) (hxb : x ≤ barrier)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, firstLowerPassage X x barrier ω = 0 := by
  have hzero :=
    Kyprianou.Ch01.brownianLowerZeroBarrierPassageAeZero
      P X sigma gamma hsigma hB hXmeas
  filter_upwards [hzero] with ω hω
  have hmon :
      firstUpperPassage (fun t ξ => -X t ξ) (x - barrier) ω ≤
        firstUpperPassage (fun t ξ => -X t ξ) 0 ω :=
    Kyprianou.Ch01.firstUpperPassageBarrierMonotone
      (fun t ξ => -X t ξ) (x - barrier) 0
      (sub_nonpos.mpr hxb) ω
  have hle :
      firstLowerPassage X x barrier ω ≤
        firstLowerPassage X 0 0 ω := by
    rw [Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic X x barrier,
      Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic X 0 0]
    simpa only [sub_self] using hmon
  have hle0 : firstLowerPassage X x barrier ω ≤
      (0 : WithTop ℝ≥0) := by
    simpa only [hω] using hle
  exact le_antisymm hle0 bot_le
