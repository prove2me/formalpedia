-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_lower_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:25.629794+00:00
-- url     : https://prove2.me/submissions/35a53be5-205d-4e4f-b722-2add87eddf2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Right continuity puts the value at a finite strict lower hitting clock in the closed negative half-line. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (w : Ω) (t : NNReal)
    (ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (t : WithTop NNReal)) :
    L.X t w ≤ 0 := by
  by_contra hn
  have hp : 0 < L.X t w := lt_of_not_ge hn
  have hrc := (L.rightCont w t).tendsto
  have hmem : {s : NNReal | 0 < L.X s w} ∈ 𝓝[≥] t :=
    hrc (Ioi_mem_nhds hp)
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hmem
  obtain ⟨U,hU,hsub⟩ := hmem
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  let u : NNReal := t + ⟨ε / 2, by positivity⟩
  have htu : t < u := by
    change t < t + _
    exact lt_add_of_pos_right _ (by exact_mod_cast (half_pos hε))
  have hex : ∃ a ∈ ((fun s : NNReal => (s : WithTop NNReal)) ''
      {s : NNReal | 0 < s ∧ L.X s w ∈ Iio 0}), a < (u : WithTop NNReal) := by
    apply sInf_lt_iff.mp
    change Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w < (u : WithTop NNReal)
    rw [ht]
    exact WithTop.coe_lt_coe.mpr htu
  obtain ⟨_,⟨s,hs,rfl⟩,hsu⟩ := hex
  have hts : t ≤ s := by
    apply WithTop.coe_le_coe.mp
    rw [← ht]
    exact sInf_le ⟨s,hs,rfl⟩
  have hsuR := WithTop.coe_lt_coe.mp hsu
  have hdist : dist s t < ε := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hts))]
    have hh : (s : ℝ) < (u : ℝ) := by exact_mod_cast hsuR
    change (s : ℝ) < (t : ℝ) + ε / 2 at hh
    linarith
  have hpos := hsub ⟨hball hdist,hts⟩
  have hposR : 0 < L.X s w := hpos
  have hnegR : L.X s w < 0 := hs.2
  linarith
