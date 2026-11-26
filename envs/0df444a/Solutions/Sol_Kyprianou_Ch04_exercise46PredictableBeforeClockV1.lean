-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PredictableBeforeClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:47.905796+00:00
-- url     : https://prove2.me/submissions/e1df07fc-c83b-4593-9ee5-e86d268ec148

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G A) :
    MeasurableSet[G.predictable] {p : NNReal × Omega | (p.1 : WithTop NNReal) ≤ A p.2} := by
  obtain ⟨D, hc, hd⟩ := TopologicalSpace.exists_countable_dense NNReal
  let : Countable D := hc.to_subtype
  have he : {p : NNReal × Omega | A p.2 < (p.1 : WithTop NNReal)} =
      ⋃ q : D, Ioi q.1 ×ˢ {w | A w ≤ (q.1 : WithTop NNReal)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Ioi]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
      have hlt : a < p.1 := WithTop.coe_lt_coe.mp (ha ▸ h)
      obtain ⟨q, hq, hqa, hqp⟩ := hd.exists_between hlt
      exact ⟨⟨q,hq⟩, hqp, by rw [← ha]; exact_mod_cast hqa.le⟩
    · rintro ⟨q,hq,ha⟩
      exact ha.trans_lt (WithTop.coe_lt_coe.mpr hq)
  have hm : MeasurableSet[G.predictable] {p : NNReal × Omega |
      A p.2 < (p.1 : WithTop NNReal)} := by
    rw [he]
    exact MeasurableSet.iUnion fun q => measurableSet_predictable_Ioi_prod (hA q.1)
  simpa only [compl_ofPred, not_lt] using hm.compl
