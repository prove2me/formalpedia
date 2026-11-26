-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49FiniteClockVersionV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:46.749039+00:00
-- url     : https://prove2.me/submissions/5b843970-e709-49eb-b001-4559ce4a4c36

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_levyJointMeasurableVersionV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockEqV3
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockMeasurableV3
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A measurable representative of the finite strict passage clock. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (a : ℝ) (ha : 0 ≤ a) :
    let τ : Ω → WithTop NNReal := fun ω => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ a + X t ω < 0}
    ∃ f : Ω → NNReal, Measurable f ∧
      ∀ᵐ ω ∂P, τ ω ≠ ⊤ → τ ω = (f ω : WithTop NNReal) := by
  classical
  obtain ⟨Z, hZ, he⟩ := levyJointMeasurableVersionV1 P X hX
  let Y : NNReal → Ω → ℝ := fun t ω => a + Z t ω
  have hm (t : NNReal) : Measurable (Y t) :=
    measurable_const.add (hZ.comp (measurable_const.prodMk measurable_id))
  let C : Ω → WithTop NNReal := fun ω => ⨅ q : ℚ,
    if 0 < (q : ℝ) ∧ Y (Real.toNNReal q) ω < 0 then
      (↑(Real.toNNReal q) : WithTop NNReal) else ⊤
  refine ⟨fun ω => (C ω).untopD 0,
    (WithTop.measurable_untopD 0).comp (exercise49RationalClockMeasurableV3 Y hm), ?_⟩
  filter_upwards [he, hX.cadlag_ae] with ω hEq hc
  have h0 : 0 ≤ a + X 0 ω := by simpa [congrFun hX.start_zero ω] using ha
  have hr (t : NNReal) : ContinuousWithinAt (fun u => a + X u ω) (Ici t) t :=
    continuousWithinAt_const.add (hc t).1
  have hC : (sInf {v : WithTop NNReal | ∃ t : NNReal,
    v = ↑t ∧ 0 < t ∧ a + X t ω < 0}) = C ω := by
    simpa only [C, Y, hEq] using exercise49RationalClockEqV3 (fun t => a + X t ω) h0 hr
  intro hfin
  change (sInf {v : WithTop NNReal | ∃ t : NNReal,
    v = ↑t ∧ 0 < t ∧ a + X t ω < 0}) = ↑((C ω).untopD 0)
  rw [hC]
  have hn : C ω ≠ ⊤ := by rwa [← hC]
  cases hcv : C ω with
  | top => exact (hn hcv).elim
  | coe c => rfl
