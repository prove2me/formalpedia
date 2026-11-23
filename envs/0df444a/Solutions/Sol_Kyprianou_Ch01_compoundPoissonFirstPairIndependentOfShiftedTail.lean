-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstPairIndependentOfShiftedTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:20:21.405199+00:00
-- url     : https://prove2.me/submissions/a052ed2c-ee5d-48c0-a295-29a0fe2a6fe6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_iIndepFunFirstPairFiniteCylinderProjection
import Theorems.Thm_Kyprianou_Ch01_firstPairIndepOfEveryFiniteShiftedTailCylinder
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q := by
  let f : (ℕ ⊕ ℕ) → Ω → ℝ :=
    fun i w => (Sum.elim arrival marks i) w
  have hMeas (i : ℕ ⊕ ℕ) : Measurable (f i) := by
    cases i with
    | inl n => exact hdriver.measurable_interarrival n
    | inr n => exact hdriver.measurable_mark n
  have hFinite (I : Finset (ℕ ⊕ ℕ)) :
      IndepFun
        (fun w => (arrival 0 w, marks 0 w))
        (fun w (i : I) => match i.val with
          | Sum.inl n => arrival (n + 1) w
          | Sum.inr n => marks (n + 1) w) Q := by
    have h :=
      Kyprianou.Ch01.iIndepFunFirstPairFiniteCylinderProjection
        Q f hdriver.indep hMeas I
    have hTail :
        (fun w (i : I) =>
          f (Sum.map Nat.succ Nat.succ i.val) w) =
        (fun w (i : I) => match i.val with
          | Sum.inl n => arrival (n + 1) w
          | Sum.inr n => marks (n + 1) w) := by
      funext w i
      cases i.val <;> rfl
    rw [hTail] at h
    exact h
  exact Kyprianou.Ch01.firstPairIndepOfEveryFiniteShiftedTailCylinder
    Q arrival marks hdriver.measurable_interarrival
      hdriver.measurable_mark hFinite
