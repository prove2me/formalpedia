-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ClockMaskPredictableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:47.559029+00:00
-- url     : https://prove2.me/submissions/e41bdd3a-02c3-4afb-a5f9-8246742d9ded

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) (T : NNReal) :
    MeasurableSet[G.rightCont.predictable]
      {p : NNReal × Omega | 0 < p.1 ∧ p.1 ≤ T ∧ (p.1 : WithTop NNReal) ≤ A p.2} := by
  have h1 := ripple_stopping_region_predictable G.rightCont A hA
  have h2 : MeasurableSet[G.rightCont.predictable] (Ioc (0 : NNReal) T ×ˢ (univ : Set Omega)) :=
    measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ
  convert h1.inter h2 using 1
  ext p
  simp [and_assoc,and_left_comm,and_comm]
