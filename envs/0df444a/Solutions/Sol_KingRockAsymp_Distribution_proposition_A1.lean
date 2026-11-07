-- Prove2me | solution 1 for KingRockAsymp.Distribution.proposition_A1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:35:22.65707+00:00
-- url     : https://prove2.me/submissions/79814c8f-2efc-4790-9124-ebc976c5fd01

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution

theorem solution {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (f : S → C(↥U, Rn m))
    (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hP3 : ∃ x : ↥U, MemLp (fun ω => f (s 0 ω) x) 2 P)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    Measurable f := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ↥U
  haveI : Countable D := hDc.to_subtype
  -- the sup distance can be computed on the countable dense set `D`
  have hedist : ∀ (σ : S) (g : C(↥U, Rn m)),
      edist (f σ) g = ⨆ x : D, edist (f σ (x : ↥U)) (g x) := by
    intro σ g
    rw [ContinuousMap.edist_eq_iSup]
    apply le_antisymm
    · apply iSup_le
      intro x
      have hcl : IsClosed {y : ↥U | edist (f σ y) (g y) ≤ ⨆ x : D, edist (f σ (x : ↥U)) (g x)} :=
        isClosed_le ((f σ).continuous.edist g.continuous) continuous_const
      have hsub : D ⊆ {y : ↥U | edist (f σ y) (g y) ≤ ⨆ x : D, edist (f σ (x : ↥U)) (g x)} :=
        fun y hy => le_iSup (fun x : D => edist (f σ (x : ↥U)) (g x)) ⟨y, hy⟩
      have := hcl.closure_subset_iff.mpr hsub
      rw [hDd.closure_eq] at this
      exact this (mem_univ x)
    · exact iSup_le fun x => le_iSup (fun y : ↥U => edist (f σ y) (g y)) (x : ↥U)
  have hmeasE : ∀ g : C(↥U, Rn m), Measurable (fun σ => edist (f σ) g) := by
    intro g
    simp_rw [hedist]
    exact Measurable.iSup fun x => (hmeas x).edist measurable_const
  have hball : ∀ (g : C(↥U, Rn m)) (r : ℝ), MeasurableSet (f ⁻¹' ball g r) := by
    intro g r
    have : f ⁻¹' ball g r = (fun σ => edist (f σ) g) ⁻¹' Iio (ENNReal.ofReal r) := by
      ext σ
      simp only [mem_preimage, mem_ball, mem_Iio]
      rw [edist_dist]
      by_cases hr : 0 < r
      · exact (ENNReal.ofReal_lt_ofReal_iff hr).symm
      · push_neg at hr
        rw [ENNReal.ofReal_of_nonpos hr]
        simp only [not_lt_zero, iff_false, not_lt]
        exact hr.trans dist_nonneg
    rw [this]
    exact hmeasE g measurableSet_Iio
  apply measurable_of_isOpen
  intro O hO
  set B : Set (Set C(↥U, Rn m)) := {b | ∃ g r, b = ball g r ∧ b ⊆ O} with hB
  obtain ⟨T, hTc, hTB, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable B (by
    rintro b ⟨g, r, rfl, -⟩; exact isOpen_ball)
  have hOeq : O = ⋃₀ B := by
    apply subset_antisymm
    · intro g hg
      obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO g hg
      exact ⟨ball g r, ⟨g, r, rfl, hrO⟩, mem_ball_self hr⟩
    · rintro g ⟨b, ⟨g', r, rfl, hbO⟩, hgb⟩
      exact hbO hgb
  rw [hOeq, ← hTU, preimage_sUnion]
  refine MeasurableSet.biUnion hTc fun b hb => ?_
  obtain ⟨g, r, rfl, -⟩ := hTB hb
  exact hball g r
