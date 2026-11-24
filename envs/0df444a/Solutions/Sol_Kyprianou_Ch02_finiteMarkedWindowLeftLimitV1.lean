-- Prove2me | solution 1 for Kyprianou.Ch02.finiteMarkedWindowLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:04:59.153357+00:00
-- url     : https://prove2.me/submissions/82fb7280-9028-4b16-a452-dea4d813502c

import Theorems.Thm_Kyprianou_Ch02_integrableMarkedTimeWindowLeftLimitV1
import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfinite : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤) :
    Tendsto (fun s : ℝ≥0 => ∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), z.2 ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ)) := by
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B
  let m := μ.restrict R
  let f : ℝ × ℝ → ℝ := fun z => z.2
  letI : IsFiniteMeasure m := ⟨by
    change μ.restrict R Set.univ < ⊤
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hfinite⟩
  have hnorm : ∀ᵐ z ∂m, ‖f z‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem (μ := μ) (measurableSet_Ioc.prod hB)] with z hz
    simpa only [f, Real.norm_eq_abs] using (show |z.2| < 1 from hsmall hz.2).le
  have hi : Integrable f m :=
    Integrable.of_bound continuous_snd.measurable.aestronglyMeasurable 1 hnorm
  let A (s : ℝ≥0) : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B
  let L : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B
  have heq (S : Set (ℝ × ℝ)) (hm : MeasurableSet S) (hs : S ⊆ R) :
      (∫ z in S, f z ∂m) = ∫ z in S, f z ∂μ := by
    change (∫ z, f z ∂(μ.restrict R).restrict S) = _
    rw [Measure.restrict_restrict hm, Set.inter_eq_left.mpr hs]
  have hl : L ⊆ R := fun z hz =>
    ⟨⟨hz.1.1, hz.1.2.le.trans (by exact_mod_cast htT)⟩, hz.2⟩
  have hconv := Kyprianou.Ch02.integrableMarkedTimeWindowLeftLimitV1 m B hB f hi t
  rw [show (∫ z in L, f z ∂m) = ∫ z in L, f z ∂μ from
    heq L (measurableSet_Ioo.prod hB) hl] at hconv
  apply hconv.congr'
  have hnear : ∀ᶠ s in nhdsWithin t (Set.Iio t), s ∈ Set.Iio t := self_mem_nhdsWithin
  filter_upwards [hnear] with s hs
  have hst : s < t := hs
  exact heq (A s) (measurableSet_Ioc.prod hB) (fun z hz =>
    ⟨⟨hz.1.1, hz.1.2.trans (by exact_mod_cast hst.le.trans htT)⟩, hz.2⟩)
