-- Prove2me | solution 1 for HessianDamping.DINAVD.vFun_hasDerivWithinAt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:13:29.153261+00:00
-- url     : https://prove2.me/submissions/428f4499-5910-4450-9902-f028e1880110

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

open Set Filter MeasureTheory

open HessianDamping.DINAVD in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β b dβ dw : ℝ → ℝ)
    (hβnn : ∀ t ∈ Ici t₀, 0 ≤ β t) (hbnn : ∀ t ∈ Ici t₀, 0 ≤ b t)
    (hβc : ContinuousOn β (Ici t₀)) (hbc : ContinuousOn b (Ici t₀))
    (hdβ : ∀ t ∈ Ici t₀, HasDerivWithinAt β (dβ t) (Ici t₀) t)
    (hdw : ∀ t ∈ Ici t₀, HasDerivWithinAt (wFun b β dβ) (dw t) (Ici t₀) t)
    (α : ℝ) (hα : 1 ≤ α)
    (x xd xdd : ℝ → H) (hx : IsSolution f α β b t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, HasDerivWithinAt (vFun f α β xstar x xd)
      ((t * (dβ t + β t / t - b t)) • gradient f (x t)) (Ici t₀) t := by
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht
  have hgd : Differentiable ℝ (gradient f) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hfC2.fderiv_right (by norm_num)
    have he : gradient f = fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f y) := rfl
    rw [he]
    exact ((InnerProductSpace.toDual ℝ H).symm.contDiff.comp h1).differentiable (by norm_num)
  obtain ⟨hX, hXd, hE⟩ := hx t ht
  have hG : HasDerivWithinAt (gradient f ∘ x) (fderiv ℝ (gradient f) (x t) (xd t)) (Ici t₀) t :=
    (hgd (x t)).hasFDerivAt.comp_hasDerivWithinAt t hX
  have key : HasDerivWithinAt (vFun f α β xstar x xd) _ (Ici t₀) t :=
    ((hX.sub_const xstar).const_smul (α - 1)).add
      ((hasDerivWithinAt_id t (Ici t₀)).smul (hXd.add ((hdβ t ht).smul hG)))
  refine key.congr_deriv ?_
  obtain ⟨D, hD⟩ : ∃ D, D = fderiv ℝ (gradient f) (x t) (xd t) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = gradient f (x t) := ⟨_, rfl⟩
  rw [← hD] at hE ⊢
  rw [← hg] at hE ⊢
  have hxdd : xdd t = -((α / t) • xd t + β t • D + b t • g) := by
    rw [eq_neg_iff_add_eq_zero, ← hE]
    abel
  have hta : t * (α / t) = α := by field_simp
  have hxdd' : t • xdd t = -(α • xd t + (t * β t) • D + (t * b t) • g) := by
    rw [hxdd, smul_neg, smul_add, smul_add, smul_smul, smul_smul, smul_smul, hta]
  have hs : t * (dβ t + β t / t - b t) = t * dβ t + β t - t * b t := by
    rw [mul_sub, mul_add, mul_div_cancel₀ _ htpos.ne']
  rw [hs]
  simp only [id, Function.comp, smul_add, one_smul]
  rw [hxdd']
  module
