-- Prove2me | solution 1 for MilnorDynamics.disk_cover_proper_and_local
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:02:19.875409+00:00
-- url     : https://prove2.me/submissions/d6f8a58f-759e-4ff4-947d-79586a7f2ef1

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

section Helpers8e

/-- The open unit disc in `ℂ` is not compact. -/
theorem ball_not_compact_8e : ¬ IsCompact (Metric.ball (0 : ℂ) 1) := by
  intro h
  have hcl : IsClosed (Metric.ball (0 : ℂ) 1) := h.isClosed
  have h1 : (1 : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    simp
  rw [hcl.closure_eq] at h1
  simp at h1

end Helpers8e

open scoped OnePoint in
open Filter Set in
theorem solution : ¬ (∀ {p : ℂ → ℂ}
    (hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))
    (hdiff : DifferentiableOn ℂ p (Metric.ball 0 1)),
    IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) ∧
      IsLocalHomeomorph (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))) := by
  intro h
  have hp : MapsTo (fun _ : ℂ => (2 : ℂ)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := by
    intro z _
    norm_num
  obtain ⟨hprop, -⟩ := h (p := fun _ : ℂ => (2 : ℂ)) hp (differentiableOn_const _)
  have hc := hprop.isCompact_preimage
    (isCompact_singleton (x := (⟨2, hp (Metric.mem_ball_self one_pos)⟩ : ({0, 1}ᶜ : Set ℂ))))
  have hpre : (hp.restrict (fun _ : ℂ => (2 : ℂ)) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) ⁻¹'
      {(⟨2, hp (Metric.mem_ball_self one_pos)⟩ : ({0, 1}ᶜ : Set ℂ))} = univ := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_univ, iff_true]
    exact Subtype.ext rfl
  rw [hpre] at hc
  have hball : IsCompact (Metric.ball (0 : ℂ) 1) := by
    have := hc.image continuous_subtype_val
    rwa [image_univ, Subtype.range_coe] at this
  exact ball_not_compact_8e hball
