-- Prove2me | solution 1 for MasulloGRH.isDSequence_openSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:21:13.379796+00:00
-- url     : https://prove2.me/submissions/93c1f41f-a9cf-4bf3-ab48-997dad4b8f07

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

open MasulloGRH

theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (U : ℕ → Set H) (C : ℝ) :
    (IsDSequence (μ.comap (Subtype.val : H → G)) U C ↔
        IsDSequence μ (fun k => Subtype.val '' U k) C) ∧
      (IsDPrimeSequence (μ.comap (Subtype.val : H → G)) U C ↔
        IsDPrimeSequence μ (fun k => Subtype.val '' U k) C) ∧
      ((∀ k, IsOpen (U k)) ↔ ∀ k, IsOpen (Subtype.val '' U k : Set G)) ∧
      ((∀ k, (U k)⁻¹ = U k) ↔
        ∀ k, (Subtype.val '' U k : Set G)⁻¹ = Subtype.val '' U k) := by
  have hHm : MeasurableSet (H : Set G) := hH.measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hHm
  have hmeas (s : Set H) : μ.comap (Subtype.val : H → G) s = μ (Subtype.val '' s) :=
    hemb.comap_apply μ s
  have hnull (s : Set H) :
      NullMeasurableSet s (μ.comap (Subtype.val : H → G)) ↔
        NullMeasurableSet (Subtype.val '' s) μ := by
    refine ⟨fun hs ↦ Measure.NullMeasurableSet.subtype_coe (s := (H : Set G))
      hHm.nullMeasurableSet hs, fun hs ↦ ?_⟩
    have hqmp : Measure.QuasiMeasurePreserving (Subtype.val : H → G)
        (μ.comap (Subtype.val : H → G)) μ :=
      ⟨measurable_subtype_coe, by
        rw [hemb.map_comap]
        exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self⟩
    simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hs.preimage hqmp
  have hone (s : Set H) : (1 : H) ∈ s ↔ (1 : G) ∈ Subtype.val '' s :=
    (Subtype.val_injective.mem_set_image (a := (1 : H))).symm
  have hdiff (s : Set H) :
      Subtype.val '' (s * s⁻¹) = (Subtype.val '' s : Set G) * (Subtype.val '' s)⁻¹ := by
    have h := Set.image_mul (m := (H : Subgroup G).subtype) (s := s) (t := s⁻¹)
    rw [Set.image_inv] at h
    exact h
  have hsub (s t : Set H) : s ⊆ t ↔ (Subtype.val '' s : Set G) ⊆ Subtype.val '' t :=
    (Set.image_subset_image_iff Subtype.val_injective).symm
  have h1 : IsDSequence (μ.comap (Subtype.val : H → G)) U C ↔
        IsDSequence μ (fun k => Subtype.val '' U k) C := by
    constructor
    · intro h
      refine ⟨fun k => (hone _).mp (h.one_mem k), fun k => (hnull _).mp (h.nullMeasurable k),
        fun k => ?_, fun k => ?_, fun k => (hsub _ _).mp (h.antitone k), h.const_pos, fun k => ?_⟩
      · have := h.measure_pos k; rwa [hmeas] at this
      · have := h.measure_lt_top k; rwa [hmeas] at this
      · have := h.doubling k; rwa [hmeas, hmeas, hdiff] at this
    · intro h
      refine ⟨fun k => (hone _).mpr (h.one_mem k), fun k => (hnull _).mpr (h.nullMeasurable k),
        fun k => ?_, fun k => ?_, fun k => (hsub _ _).mpr (h.antitone k), h.const_pos, fun k => ?_⟩
      · rw [hmeas]; exact h.measure_pos k
      · rw [hmeas]; exact h.measure_lt_top k
      · rw [hmeas, hmeas, hdiff]; exact h.doubling k
  have hopen : Topology.IsOpenEmbedding (Subtype.val : H → G) := hH.isOpenEmbedding_subtypeVal
  refine ⟨h1, ?_, ?_, ?_⟩
  · refine and_congr h1 ⟨fun h W hW ↦ ?_, fun h W hW ↦ ?_⟩
    · obtain ⟨k, hk⟩ := h _ (continuous_subtype_val.continuousAt.preimage_mem_nhds hW)
      exact ⟨k, Set.image_subset_iff.mpr hk⟩
    · obtain ⟨k, hk⟩ := h _ (hopen.image_mem_nhds.mpr hW)
      exact ⟨k, (Set.image_subset_image_iff Subtype.val_injective).mp hk⟩
  · exact forall_congr' fun _ ↦ hopen.isOpen_iff_image_isOpen
  · have key (s : Set H) : (Subtype.val '' s : Set G)⁻¹ = Subtype.val '' s⁻¹ := by
      ext x
      simp only [Set.mem_inv, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact ⟨y⁻¹, by simpa using hy, by simp [hyx]⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, hy, by simp⟩
    exact forall_congr' fun k ↦ by rw [key, Subtype.val_injective.image_injective.eq_iff]
