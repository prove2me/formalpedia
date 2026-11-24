-- Prove2me | solution 1 for Kyprianou.Ch03.levyNoFixedTimeJumpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:19:22.460405+00:00
-- url     : https://prove2.me/submissions/b49388f9-31e8-4967-a299-3e76e3b6f378

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_levyFixedTimeIncrementLimitLawV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (u : NNReal) (hu : 0 < u) :
    ∀ᵐ ω ∂P, Function.leftLim (fun r : NNReal => X r ω) u = X u ω := by
  let D (ω : Omega) := X u ω - Function.leftLim (fun r : NNReal => X r ω) u
  have h := (Kyprianou.Ch03.levyFixedTimeIncrementLimitLawV1 P X hX u hu).comp
    (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
  have hD : IdentDistrib D (fun _ : Omega => (0 : ℝ)) P P := h
  have hz : P {ω | D ω ≠ 0} = 0 := by
    have hh := congrArg (fun m : Measure ℝ => m ({(0 : ℝ)}ᶜ)) hD.map_eq
    rw [Measure.map_apply_of_aemeasurable hD.aemeasurable_fst
      (measurableSet_singleton _).compl] at hh
    simpa [Measure.map_const, Set.preimage] using hh
  have ha : ∀ᵐ ω ∂P, D ω = 0 := ae_iff.mpr (by simpa using hz)
  filter_upwards [ha] with ω hω
  exact (sub_eq_zero.mp hω).symm
