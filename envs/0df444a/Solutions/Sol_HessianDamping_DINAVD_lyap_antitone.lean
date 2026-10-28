-- Prove2me | solution 1 for HessianDamping.DINAVD.lyap_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:02:13.815557+00:00
-- url     : https://prove2.me/submissions/dfce88a2-9355-4412-bf06-114735119b06

import Mathlib
import Definitions.Def_HessianDamping_DINAVD_Setting

open Set Filter MeasureTheory

namespace Aux_HD_anti

open scoped InnerProductSpace

lemma grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hconv : ConvexOn ℝ Set.univ f) (x : H) (hd : DifferentiableAt ℝ f x) (y : H) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  set d := y - x with hdd
  have hline : HasDerivAt (fun s : ℝ => x + s • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hφ : HasDerivAt (fun s : ℝ => f (x + s • d)) (⟪gradient f x, d⟫_ℝ) 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd.hasFDerivAt hline (by simp)
    refine this.congr_deriv ?_
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hslope := hφ.tendsto_slope_zero_right
  have hle : ⟪gradient f x, d⟫_ℝ ≤ f y - f x := by
    apply le_of_tendsto hslope
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have hs0 : 0 < s := hs.1
    have hc := hconv.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith [hs.2] : (0:ℝ) ≤ 1 - s)
      hs0.le (by ring)
    have he : (1 - s) • x + s • y = x + s • d := by rw [hdd]; module
    rw [he, smul_eq_mul, smul_eq_mul] at hc
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ hs0]
    linarith
  linarith

end Aux_HD_anti

namespace Aux_HD_anti
open HessianDamping.DINAVD
theorem l62
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
    (hG₂ : ∀ t ∈ Ici t₀, dβ t + β t / t < b t)
    (dE : ℝ → ℝ)
    (hE : ∀ t ∈ Ici t₀, HasDerivWithinAt (lyap f α β b dβ xstar x xd) (dE t) (Ici t₀) t) :
    ∀ t ∈ Ici t₀,
      dE t + β t * deltaFun b β dβ t * ‖gradient f (x t)‖ ^ 2
        + ((α - 1) / t * deltaFun b β dβ t - deltaDeriv b β dβ dw t) * (f (x t) - f xstar)
        ≤ 0 := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ht₀ ht
  obtain ⟨hxd, hxdd, hode⟩ := hx t ht
  have hfdiff : Differentiable ℝ f := hfC2.differentiable (by norm_num)
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ f) := hfC2.fderiv_right (by norm_num)
  have hgrad_eq : gradient f = fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f y) := rfl
  have hgradC1 : ContDiff ℝ 1 (gradient f) := by
    rw [hgrad_eq]; exact (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfd1
  have hgdiff : Differentiable ℝ (gradient f) := hgradC1.differentiable one_ne_zero
  set S := Ici t₀ with hS
  set g := gradient f (x t) with hg
  set h := fderiv ℝ (gradient f) (x t) (xd t) with hh
  -- derivatives of the pieces
  have dfx : HasDerivWithinAt (fun s => f (x s)) (inner ℝ g (xd t)) S t := by
    have := (hfdiff (x t)).hasFDerivAt.comp_hasDerivWithinAt t hxd
    refine this.congr_deriv ?_
    rw [hg, gradient, InnerProductSpace.toDual_symm_apply]
  have dgx : HasDerivWithinAt (fun s => gradient f (x s)) h S t :=
    (hgdiff (x t)).hasFDerivAt.comp_hasDerivWithinAt t hxd
  have dδ : HasDerivWithinAt (deltaFun b β dβ) (deltaDeriv b β dβ dw t) S t := by
    have := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := S)).mul (hdw t ht)
    refine this.congr_deriv ?_
    unfold deltaDeriv
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  -- ODE multiplied by t
  have hαt : t * (α / t) = α := mul_div_cancel₀ α ht0.ne'
  have hode2 : t • xdd t + α • xd t + (t * β t) • h + (t * b t) • g = 0 := by
    have := congrArg (fun v => t • v) hode
    simp only [smul_add, smul_smul, smul_zero, hαt] at this
    exact this
  set c := β t - t * b t + t * dβ t with hc
  have dv : HasDerivWithinAt (vFun f α β xstar x xd) (c • g) S t := by
    have h1 := (hxd.sub_const xstar).const_smul (α - 1)
    have h2 := (hasDerivWithinAt_id t S).smul (hxdd.add ((hdβ t ht).smul dgx))
    have := h1.add h2
    refine this.congr_deriv ?_
    simp only [id, Pi.add_apply, Pi.smul_apply, Pi.smul_apply']
    rw [← hg, hc]
    linear_combination (norm := module) hode2
  have dE' : HasDerivWithinAt (lyap f α β b dβ xstar x xd)
      (deltaDeriv b β dβ dw t * (f (x t) - f xstar) + deltaFun b β dβ t * inner ℝ g (xd t)
        + 1 / 2 * (2 * inner ℝ (vFun f α β xstar x xd t) (c • g))) S t :=
    (dδ.mul (dfx.sub_const (f xstar))).add (dv.norm_sq.const_mul (1 / 2))
  have huniq : dE t = deltaDeriv b β dβ dw t * (f (x t) - f xstar) +
      deltaFun b β dβ t * inner ℝ g (xd t) +
        1 / 2 * (2 * inner ℝ (vFun f α β xstar x xd t) (c • g)) :=
    (uniqueDiffOn_Ici t₀ t ht).eq_deriv _ (hE t ht) dE'
  -- delta in terms of c
  have hδ : deltaFun b β dβ t = -(t * c) := by
    unfold deltaFun wFun
    rw [hc]
    field_simp
    ring
  have hδpos : 0 < deltaFun b β dβ t := by
    unfold deltaFun wFun
    have := hG₂ t ht
    have : 0 < b t - dβ t - β t / t := by linarith
    positivity
  have hcneg : c ≤ 0 := by
    rw [hδ] at hδpos
    nlinarith
  -- inner product expansion
  have hinner : inner ℝ (vFun f α β xstar x xd t) (c • g) =
      c * ((α - 1) * inner ℝ (x t - xstar) g + t * inner ℝ (xd t) g + t * β t * ‖g‖ ^ 2) := by
    unfold vFun
    rw [real_inner_smul_right, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hg]
    ring
  -- convexity
  have hconv := Aux_HD_anti.grad_ineq f hfconv (x t) (hfdiff (x t)) xstar
  rw [← hg] at hconv
  have hI : f (x t) - f xstar ≤ inner ℝ (x t - xstar) g := by
    have : inner ℝ g (xstar - x t) = -inner ℝ (x t - xstar) g := by
      rw [← neg_sub, inner_neg_right, real_inner_comm]
    linarith
  rw [huniq, hinner, hδ, real_inner_comm (xd t) g]
  have key : deltaDeriv b β dβ dw t * (f (x t) - f xstar) + -(t * c) * inner ℝ (xd t) g +
      1 / 2 * (2 * (c * ((α - 1) * inner ℝ (x t - xstar) g + t * inner ℝ (xd t) g +
        t * β t * ‖g‖ ^ 2))) + β t * -(t * c) * ‖g‖ ^ 2 +
      ((α - 1) / t * -(t * c) - deltaDeriv b β dβ dw t) * (f (x t) - f xstar) =
      c * (α - 1) * (inner ℝ (x t - xstar) g - (f (x t) - f xstar)) := by
    field_simp
    ring
  rw [key]
  have h1 : 0 ≤ α - 1 := by linarith
  have h2 : 0 ≤ inner ℝ (x t - xstar) g - (f (x t) - f xstar) := by linarith
  have := mul_nonneg (mul_nonneg (neg_nonneg.mpr hcneg) h1) h2
  nlinarith

end Aux_HD_anti
namespace Aux_HD_anti
open HessianDamping.DINAVD
theorem lyap_deriv
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
    (hG₂ : ∀ t ∈ Ici t₀, dβ t + β t / t < b t)
    : ∀ t ∈ Ici t₀, ∃ D, HasDerivWithinAt (lyap f α β b dβ xstar x xd) D (Ici t₀) t := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ht₀ ht
  obtain ⟨hxd, hxdd, hode⟩ := hx t ht
  have hfdiff : Differentiable ℝ f := hfC2.differentiable (by norm_num)
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ f) := hfC2.fderiv_right (by norm_num)
  have hgrad_eq : gradient f = fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f y) := rfl
  have hgradC1 : ContDiff ℝ 1 (gradient f) := by
    rw [hgrad_eq]; exact (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfd1
  have hgdiff : Differentiable ℝ (gradient f) := hgradC1.differentiable one_ne_zero
  set S := Ici t₀ with hS
  set g := gradient f (x t) with hg
  set h := fderiv ℝ (gradient f) (x t) (xd t) with hh
  -- derivatives of the pieces
  have dfx : HasDerivWithinAt (fun s => f (x s)) (inner ℝ g (xd t)) S t := by
    have := (hfdiff (x t)).hasFDerivAt.comp_hasDerivWithinAt t hxd
    refine this.congr_deriv ?_
    rw [hg, gradient, InnerProductSpace.toDual_symm_apply]
  have dgx : HasDerivWithinAt (fun s => gradient f (x s)) h S t :=
    (hgdiff (x t)).hasFDerivAt.comp_hasDerivWithinAt t hxd
  have dδ : HasDerivWithinAt (deltaFun b β dβ) (deltaDeriv b β dβ dw t) S t := by
    have := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := S)).mul (hdw t ht)
    refine this.congr_deriv ?_
    unfold deltaDeriv
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  -- ODE multiplied by t
  have hαt : t * (α / t) = α := mul_div_cancel₀ α ht0.ne'
  have hode2 : t • xdd t + α • xd t + (t * β t) • h + (t * b t) • g = 0 := by
    have := congrArg (fun v => t • v) hode
    simp only [smul_add, smul_smul, smul_zero, hαt] at this
    exact this
  set c := β t - t * b t + t * dβ t with hc
  have dv : HasDerivWithinAt (vFun f α β xstar x xd) (c • g) S t := by
    have h1 := (hxd.sub_const xstar).const_smul (α - 1)
    have h2 := (hasDerivWithinAt_id t S).smul (hxdd.add ((hdβ t ht).smul dgx))
    have := h1.add h2
    refine this.congr_deriv ?_
    simp only [id, Pi.add_apply, Pi.smul_apply, Pi.smul_apply']
    rw [← hg, hc]
    linear_combination (norm := module) hode2
  have dE' : HasDerivWithinAt (lyap f α β b dβ xstar x xd)
      (deltaDeriv b β dβ dw t * (f (x t) - f xstar) + deltaFun b β dβ t * inner ℝ g (xd t)
        + 1 / 2 * (2 * inner ℝ (vFun f α β xstar x xd t) (c • g))) S t :=
    (dδ.mul (dfx.sub_const (f xstar))).add (dv.norm_sq.const_mul (1 / 2))
  exact ⟨_, dE'⟩

end Aux_HD_anti

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
    (hG₂ : ∀ t ∈ Ici t₀, dβ t + β t / t < b t)
    (hG₃ : ∀ t ∈ Ici t₀, t * dw t ≤ (α - 3) * wFun b β dβ t) :
    AntitoneOn (lyap f α β b dβ xstar x xd) (Ici t₀) ∧
    ∀ t ∈ Ici t₀, lyap f α β b dβ xstar x xd t ≤ lyap f α β b dβ xstar x xd t₀ := by
  have hder := Aux_HD_anti.lyap_deriv f hfconv hfC2 xstar hxstar t₀ ht₀ β b dβ dw hβnn hbnn hβc
    hbc hdβ hdw α hα x xd xdd hx hG₂
  set E := lyap f α β b dβ xstar x xd with hEdef
  let dE : ℝ → ℝ := fun t => derivWithin E (Ici t₀) t
  have hE : ∀ t ∈ Ici t₀, HasDerivWithinAt E (dE t) (Ici t₀) t := by
    intro t ht
    obtain ⟨D, hD⟩ := hder t ht
    exact hD.differentiableWithinAt.hasDerivWithinAt
  have hineq := Aux_HD_anti.l62 f hfconv hfC2 xstar hxstar t₀ ht₀ β b dβ dw hβnn hbnn hβc hbc
    hdβ hdw α hα x xd xdd hx hG₂ dE hE
  have hneg : ∀ t ∈ Ici t₀, dE t ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₀ ht
    have h1 := hineq t ht
    have hw : 0 < wFun b β dβ t := by
      unfold wFun; have := hG₂ t ht; linarith
    have hδ : 0 < deltaFun b β dβ t := by unfold deltaFun; positivity
    have h2 : 0 ≤ β t * deltaFun b β dβ t * ‖gradient f (x t)‖ ^ 2 := by
      have := hβnn t ht; positivity
    have h3 : 0 ≤ (α - 1) / t * deltaFun b β dβ t - deltaDeriv b β dβ dw t := by
      have e : (α - 1) / t * deltaFun b β dβ t - deltaDeriv b β dβ dw t =
          t * ((α - 3) * wFun b β dβ t - t * dw t) := by
        unfold deltaFun deltaDeriv
        field_simp
        ring
      rw [e]
      have := hG₃ t ht
      have : 0 ≤ (α - 3) * wFun b β dβ t - t * dw t := by linarith
      positivity
    have h4 : 0 ≤ f (x t) - f xstar := by linarith [hxstar (x t)]
    have h5 := mul_nonneg h3 h4
    linarith
  have hanti : AntitoneOn E (Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
    · intro t ht
      exact (hE t ht).continuousWithinAt
    · rw [interior_Ici]
      intro t ht
      exact ((hE t (Set.mem_Ioi.mp ht).le).hasDerivAt (Ici_mem_nhds ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [((hE t (Set.mem_Ioi.mp ht).le).hasDerivAt (Ici_mem_nhds ht)).deriv]
      exact hneg t (Set.mem_Ioi.mp ht).le
  refine ⟨hanti, fun t ht => hanti Set.self_mem_Ici ht ht⟩
