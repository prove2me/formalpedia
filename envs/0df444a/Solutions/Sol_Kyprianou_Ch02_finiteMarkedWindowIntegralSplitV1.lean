-- Prove2me | solution 1 for Kyprianou.Ch02.finiteMarkedWindowIntegralSplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:05:10.335467+00:00
-- url     : https://prove2.me/submissions/db28f7e3-a746-4748-aee4-8ec901bfda10

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfinite : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤) (ht : 0 < t) :
    (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) =
      (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) +
      (∫ z in ({(t : ℝ)} ×ˢ B), z.2 ∂μ) := by
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
  let D : Set (ℝ × ℝ) := {(t : ℝ)} ×ˢ B
  let L : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B
  let A : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B
  have hsub : A ⊆ R := fun z hz =>
    ⟨⟨hz.1.1, hz.1.2.trans (by exact_mod_cast htT)⟩, hz.2⟩
  have hdis : Disjoint L D := by
    refine Set.disjoint_left.2 ?_
    intro z hz hdz
    exact (ne_of_lt hz.1.2) (Set.mem_singleton_iff.mp hdz.1)
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hunion : L ∪ D = A := by
    ext z
    simp only [L, D, A, Set.mem_union, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioc,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact ⟨⟨h.1.1, h.1.2.le⟩, h.2⟩
      · exact ⟨⟨by rw [h.1]; exact ht0, h.1.le⟩, h.2⟩
    · intro h
      rcases lt_or_eq_of_le h.1.2 with hlt | heq
      · exact Or.inl ⟨⟨h.1.1, hlt⟩, h.2⟩
      · exact Or.inr ⟨heq, h.2⟩
  have hiR : IntegrableOn f R μ := hi
  have hiA : IntegrableOn f A μ := hiR.mono_set hsub
  have hiL : IntegrableOn f L μ := hiA.mono_set (by rw [← hunion]; exact Set.subset_union_left)
  have hiD : IntegrableOn f D μ := hiA.mono_set (by rw [← hunion]; exact Set.subset_union_right)
  change (∫ z in A, f z ∂μ) = (∫ z in L, f z ∂μ) + ∫ z in D, f z ∂μ
  rw [← hunion]
  exact setIntegral_union hdis ((measurableSet_singleton _).prod hB) hiL hiD
