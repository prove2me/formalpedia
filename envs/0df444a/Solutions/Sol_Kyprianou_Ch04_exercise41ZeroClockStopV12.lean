-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ZeroClockStopV12
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:05:33.065317+00:00
-- url     : https://prove2.me/submissions/a6a6290b-6b2d-41e3-a730-952e3000b1f3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41EventClockStopV13
import Theorems.Thm_Kyprianou_Ch04_exercise41CappedClockStopV13
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_iSup_countable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (X : NNReal → Ω → ℝ) (hX : Adapted F X)
    (q : ℕ → NNReal) (a N : NNReal) :
    let raw := fun w : Ω => ⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |X (q k) w| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤
    let τ := fun w => (min (raw w) (N : WithTop NNReal)).untopD 0
    ∀ s : NNReal, MeasurableSet[F.rightCont s] {w | τ w ≤ s} := by
  classical
  let T (n k : ℕ) (w : Ω) : WithTop NNReal :=
    if a ≤ q k ∧ |X (q k) w| < 1 / ((n : ℝ) + 1) then q k else ⊤
  have hT (n k : ℕ) : IsStoppingTime F.rightCont (T n k) := by
    let A : Set Ω := {w | a ≤ q k ∧ |X (q k) w| < 1 / ((n : ℝ) + 1)}
    have hA : MeasurableSet[F.rightCont (q k)] A := by
      letI : MeasurableSpace Ω := F.rightCont (q k)
      exact MeasurableSet.inter (MeasurableSet.const _)
        (measurableSet_lt ((hX (q k)).mono (F.le_rightCont (q k)) le_rfl).abs measurable_const)
    simpa only [T,A,Set.mem_setOf_eq] using exercise41EventClockStopV13 F.rightCont (q k) A hA
  have hn (n : ℕ) : IsStoppingTime F.rightCont (fun w => ⨅ k, T n k w) :=
    IsStoppingTime.iInf (hT n)
  exact exercise41CappedClockStopV13 F.rightCont _
    (isStoppingTime_iSup_countable _ hn) N
