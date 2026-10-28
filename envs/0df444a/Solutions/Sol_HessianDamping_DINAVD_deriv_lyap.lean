-- Prove2me | solution 1 for HessianDamping.DINAVD.deriv_lyap
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:16:03.160974+00:00
-- url     : https://prove2.me/submissions/23a4c14a-b6ca-4968-bc71-5fab2f7bdc58

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
    (x xd xdd : ℝ → H) (hx : IsSolution f α β b t₀ x xd xdd)
    (vd : ℝ → H)
    (hv : ∀ t ∈ Ici t₀, HasDerivWithinAt (vFun f α β xstar x xd) (vd t) (Ici t₀) t) :
    ∀ t ∈ Ici t₀, HasDerivWithinAt (lyap f α β b dβ xstar x xd)
      (deltaDeriv b β dβ dw t * (f (x t) - f xstar)
        + deltaFun b β dβ t * inner ℝ (gradient f (x t)) (xd t)
        + inner ℝ (vFun f α β xstar x xd t) (vd t)) (Ici t₀) t := by
  intro t ht
  obtain ⟨hX, -, -⟩ := hx t ht
  have hfd : Differentiable ℝ f := hfC2.differentiable (by norm_num)
  have hF : HasDerivWithinAt (f ∘ x) (fderiv ℝ f (x t) (xd t)) (Ici t₀) t :=
    (hfd (x t)).hasFDerivAt.comp_hasDerivWithinAt t hX
  have hδ : HasDerivWithinAt (deltaFun b β dβ) _ (Ici t₀) t :=
    (hasDerivWithinAt_pow 2 t (s := Ici t₀)).mul (hdw t ht)
  have key : HasDerivWithinAt (lyap f α β b dβ xstar x xd) _ (Ici t₀) t :=
    (hδ.mul (hF.sub_const (f xstar))).add ((hv t ht).norm_sq.const_mul (1 / 2))
  refine key.congr_deriv ?_
  have hin : inner ℝ (gradient f (x t)) (xd t) = fderiv ℝ f (x t) (xd t) :=
    InnerProductSpace.toDual_symm_apply
  rw [hin]
  unfold deltaDeriv deltaFun
  simp only [Function.comp]
  push_cast
  ring
