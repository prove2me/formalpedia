-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_slice_lower_hy4_finite_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:18:10.723404+00:00
-- url     : https://prove2.me/submissions/8b8e104d-80d5-491c-ae74-1296f4a97c23

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.WithBot
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    {d : ℝ} (hd : 0 < d) {ω : Ω} (hcad : IsCadlag (fun t : ℝ≥0 => D.X t ω)) :
    Kyprianou.Ch08.tauPlus D.X d ω ≠ ⊤ →
      ∃ u : ℝ≥0, (u : ℝ≥0∞) = Kyprianou.Ch08.tauPlus D.X d ω ∧ d ≤ D.X u ω := by
  intro hUtop
  cases hT : Kyprianou.Ch08.tauPlus D.X d ω with
  | top =>
      exfalso
      exact hUtop (by simpa using hT)
  | coe u =>
      have hTu : (u : WithTop ℝ≥0) = Kyprianou.Ch08.tauPlus D.X d ω := by
        simpa using hT.symm
      have hbound : d ≤ D.X u ω := by
        by_contra hnot
        have hlt : D.X u ω < d := lt_of_not_ge hnot
        have hEv : {v : ℝ≥0 | D.X v ω < d} ∈ 𝓝[Ici u] u :=
          (hcad u).1 (Iio_mem_nhds hlt)
        obtain ⟨b, hub, hbsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hEv
        have hUlt : Kyprianou.Ch08.tauPlus D.X d ω < (b : WithTop ℝ≥0) := by
          rw [← hTu]
          exact WithTop.coe_lt_coe.mpr hub
        have hsInf : sInf {t : WithTop ℝ≥0 | ∃ v : ℝ≥0,
          0 < v ∧ (v : WithTop ℝ≥0) = t ∧ d < D.X v ω} < (b : WithTop ℝ≥0) := by
          simpa [tauPlus] using hUlt
        rcases (sInf_lt_iff.mp hsInf) with ⟨t, htmem, htlt⟩
        rcases htmem with ⟨v, hv0, rfl, hvd⟩
        have huvE : (u : WithTop ℝ≥0) ≤ (v : WithTop ℝ≥0) := by
          have hle : Kyprianou.Ch08.tauPlus D.X d ω ≤ (v : WithTop ℝ≥0) := by
            unfold tauPlus
            exact sInf_le ⟨v, hv0, rfl, hvd⟩
          simpa [hTu] using hle
        have huv : u ≤ v := by exact_mod_cast huvE
        have hvlt : v < b := by exact_mod_cast htlt
        exact (not_lt_of_ge (le_of_lt hvd)) (hbsub ⟨huv, hvlt⟩)
      refine ⟨u, ?_, hbound⟩
      simpa [hT]
