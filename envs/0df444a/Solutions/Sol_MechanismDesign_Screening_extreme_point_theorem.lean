-- Prove2me | solution 1 for MechanismDesign.Screening.extreme_point_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:08:04.709983+00:00
-- url     : https://prove2.me/submissions/41853d1b-48cd-4869-96f0-6358218f26bc

import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

open MeasureTheory

namespace MechanismDesign.Screening

lemma isExtremePoint_of_mem_extremePoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} {x : E} (hx : x ∈ X.extremePoints ℝ) : IsExtremePoint X x := by
  refine ⟨hx.1, fun y hy => ?_⟩
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hseg : x ∈ openSegment ℝ (x + y) (x - y) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_sub, add_add_sub_cancel, ← add_smul]; norm_num
  have := (mem_extremePoints_iff_left.1 hx).2 _ h1 _ h2 hseg
  exact hy (by simpa using this)

theorem extreme_point_theorem_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hne : X.Nonempty) (hcomp : IsCompact X) (hconv : Convex ℝ X)
    (f : E →ₗ[ℝ] ℝ) (hf : ContinuousOn f X) :
    {e | IsExtremePoint X e}.Nonempty ∧ ∃ e, IsExtremePoint X e ∧ ∀ x ∈ X, f x ≤ f e := by
  constructor
  · obtain ⟨e, he⟩ := hcomp.extremePoints_nonempty hne
    exact ⟨e, isExtremePoint_of_mem_extremePoints he⟩
  · obtain ⟨x0, hx0, hmax⟩ := hcomp.exists_isMaxOn hne hf
    set S := X ∩ f ⁻¹' {f x0} with hS
    have hSc : IsClosed S := hf.preimage_isClosed_of_isClosed hcomp.isClosed isClosed_singleton
    have hScomp : IsCompact S := hcomp.of_isClosed_subset hSc Set.inter_subset_left
    have hSne : S.Nonempty := ⟨x0, hx0, rfl⟩
    have hext : IsExtreme ℝ X S := by
      refine ⟨Set.inter_subset_left, ?_⟩
      intro x hx y hy z hz hzs
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzs
      refine ⟨hx, ?_⟩
      have hz2 : f (a • x + b • y) = f x0 := hz.2
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hz2
      have h1 : f x ≤ f x0 := hmax hx
      have h2 : f y ≤ f x0 := hmax hy
      show f x = f x0
      by_contra hne'
      have h1' : f x < f x0 := lt_of_le_of_ne h1 hne'
      have e3 : a * f x0 + b * f x0 = f x0 := by rw [← add_mul, hab, one_mul]
      nlinarith [mul_lt_mul_of_pos_left h1' ha, mul_le_mul_of_nonneg_left h2 hb.le]
    obtain ⟨e, he⟩ := hScomp.extremePoints_nonempty hSne
    refine ⟨e, isExtremePoint_of_mem_extremePoints (hext.extremePoints_subset_extremePoints he), ?_⟩
    intro x hx
    have : f e = f x0 := (he.1).2
    rw [this]; exact hmax hx

end MechanismDesign.Screening

open MechanismDesign.Screening


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hne : X.Nonempty) (hcomp : IsCompact X) (hconv : Convex ℝ X)
    (f : E →ₗ[ℝ] ℝ) (hf : ContinuousOn f X) :
    {e | IsExtremePoint X e}.Nonempty ∧ ∃ e, IsExtremePoint X e ∧ ∀ x ∈ X, f x ≤ f e := by
  exact extreme_point_theorem_core X hne hcomp hconv f hf
