-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RecoveryGateV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:30:00.22487+00:00
-- url     : https://prove2.me/submissions/5a6b731e-8adf-4445-975c-2a1a08a3d9b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (r : NNReal) :
    MeasurableSet[G.rightCont r]
      {w | A w < (r : WithTop NNReal) ∧ (((A w).untopD 0 : NNReal) : Real) < L.X r w} := by
  let a : Omega → NNReal := fun w => (min (A w) (r : WithTop NNReal)).untopD 0
  have hcap := (hA.min_const r).measurable_of_le (fun w => min_le_right (A w) (r : WithTop NNReal))
  have ha : Measurable[G.rightCont r] a := Measurable.untopD 0 hcap
  have hX : Measurable[G.rightCont r] (L.X r) :=
    (L.adapted r).mono (G.le_rightCont r) le_rfl
  have hcmp : MeasurableSet[G.rightCont r] {w | (a w : Real) < L.X r w} :=
    measurableSet_lt (NNReal.continuous_coe.measurable.comp ha) hX
  have he : {w | A w < (r : WithTop NNReal) ∧ (((A w).untopD 0 : NNReal) : Real) < L.X r w} =
      {w | A w < (r : WithTop NNReal)} ∩ {w | (a w : Real) < L.X r w} := by
    ext w
    change (A w < (r : WithTop NNReal) ∧ (((A w).untopD 0 : NNReal) : Real) < L.X r w) ↔
      A w < (r : WithTop NNReal) ∧ (a w : Real) < L.X r w
    have hh : A w < (r : WithTop NNReal) → a w = (A w).untopD 0 := by
      intro h
      change (min (A w) (r : WithTop NNReal)).untopD 0 = (A w).untopD 0
      rw [min_eq_left h.le]
    exact ⟨fun h => ⟨h.1, by rw [hh h.1]; exact h.2⟩,
      fun h => ⟨h.1, by rw [← hh h.1]; exact h.2⟩⟩
  rw [he]
  exact (hA.measurableSet_lt r).inter hcmp
