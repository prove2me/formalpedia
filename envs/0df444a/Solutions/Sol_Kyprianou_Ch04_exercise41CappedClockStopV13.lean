-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CappedClockStopV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:05:07.361548+00:00
-- url     : https://prove2.me/submissions/de83c041-5a16-496f-8ce3-63c1f86cbc78

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (F : Filtration NNReal inferInstance)
    (raw : Ω → WithTop NNReal) (hr : IsStoppingTime F raw) (N : NNReal) :
    ∀ s : NNReal, MeasurableSet[F s] {w | (min (raw w) (N : WithTop NNReal)).untopD 0 ≤ s} := by
  have hcap := hr.min_const N
  have hcoe (w : Ω) :
      (↑((min (raw w) (N : WithTop NNReal)).untopD (0 : NNReal)) : WithTop NNReal) =
      min (raw w) (N : WithTop NNReal) := by
    have hf : min (raw w) (N : WithTop NNReal) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top N))
    cases h : min (raw w) (N : WithTop NNReal) with
    | top => exact False.elim (hf h)
    | coe a => rfl
  intro s
  have he : {w | (min (raw w) (N : WithTop NNReal)).untopD 0 ≤ s} =
      {w | min (raw w) (N : WithTop NNReal) ≤ (s : WithTop NNReal)} := by
    ext w
    change (min (raw w) (N : WithTop NNReal)).untopD 0 ≤ s ↔
      min (raw w) (N : WithTop NNReal) ≤ (s : WithTop NNReal)
    exact WithTop.coe_le_coe.symm.trans (by rw [hcoe w])
  rw [he]
  exact hcap s
