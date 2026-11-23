-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonDriverShiftedTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:34:08.274973+00:00
-- url     : https://prove2.me/submissions/7baad6ed-091c-40b0-80b1-2edbf72985b4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
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
    IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w)
      rate jumpLaw Q := by
  let shift : (ℕ ⊕ ℕ) → (ℕ ⊕ ℕ) :=
    Sum.elim (fun n => Sum.inl (n + 1)) (fun n => Sum.inr (n + 1))
  have hInj : Function.Injective shift := by
    intro a b hab
    cases a <;> cases b <;> simp_all [shift]
  refine {
    measurable_interarrival := fun n => hdriver.measurable_interarrival (n + 1)
    measurable_mark := fun n => hdriver.measurable_mark (n + 1)
    indep := ?_
    law_interarrival := fun n => hdriver.law_interarrival (n + 1)
    law_mark := fun n => hdriver.law_mark (n + 1)
  }
  have hFamily :
      (Sum.elim (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w)) =
        (fun i => (Sum.elim arrival marks) (shift i)) := by
    funext i
    cases i <;> rfl
  rw [hFamily]
  exact hdriver.indep.precomp hInj
