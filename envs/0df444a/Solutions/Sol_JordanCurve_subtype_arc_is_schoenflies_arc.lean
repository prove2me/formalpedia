-- Prove2me | solution 1 for JordanCurve.subtype_arc_is_schoenflies_arc
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T07:58:24.37508+00:00
-- url     : https://prove2.me/submissions/edd91161-1ed3-4a49-b47c-39214df99e2b

import Definitions.Def_SchoenfliesCurveCore

open Set unitInterval

theorem solution
    (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    Schoenflies.IsArc (Set.range α) := by
  let f : ℝ → Schoenflies.Plane := fun t =>
    if ht : t ∈ I then α ⟨t, ht⟩ else 0
  have hf_eq (t : ℝ) (ht : t ∈ I) : f t = α ⟨t, ht⟩ := by
    simp only [f, dif_pos ht]
  have hf : ContinuousOn f I := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (I : Set ℝ).domRestrict f = α := by
      funext t
      exact hf_eq t.1 t.2
    simpa only [heq] using hα
  have hfi : InjOn f I := by
    intro x hx y hy hxy
    have hxy' : α ⟨x, hx⟩ = α ⟨y, hy⟩ := by
      simpa only [hf_eq x hx, hf_eq y hy] using hxy
    exact congrArg Subtype.val (hinj hxy')
  have hfr : f '' I = Set.range α := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (hf_eq t ht).symm⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      exact ⟨t, ht, hf_eq t ht⟩
  exact ⟨f, hf, hfi, hfr⟩
