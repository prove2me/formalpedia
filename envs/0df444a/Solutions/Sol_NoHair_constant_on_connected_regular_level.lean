-- Prove2me | solution 1 for NoHair.constant_on_connected_regular_level
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:25:28.132463+00:00
-- url     : https://prove2.me/submissions/547a3465-1c24-4ac5-beb4-7a66ba10bab3

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev X := ADMPoint

set_option maxHeartbeats 700000 in
theorem solution (W S : Set ADMPoint) (N f : ADMPoint → ℝ)
    (hs : IsConnected S) (hw : IsOpen W) (hsub : S ⊆ W)
    (hN : ContDiffOn ℝ 1 N W) (hf : DifferentiableOn ℝ f W)
    (hreg : ∀ x ∈ S, fderiv ℝ N x ≠ 0)
    (hlevel : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, y ∈ S ↔ N y = 0)
    (hzero : ∀ x ∈ S, fderiv ℝ f x = 0) : ∀ x ∈ S, ∀ y ∈ S, f x = f y := by
  classical
  have local_eq (a : X) (ha : a ∈ S) : ∀ᶠ y in 𝓝 a, y ∈ S → f y = f a := by
    let L := fderiv ℝ N a
    obtain ⟨u,hu⟩ : ∃ u : X, L u ≠ 0 := by
      by_contra! hc
      apply hreg a ha
      ext u
      exact hc u
    let v := (L u)⁻¹ • u
    have hv : L v=1 := by simp [v,hu]
    let F := fun y : X => y+(N y - L y) • v
    have lev (y : X) : L (F y) = N y := by
      dsimp only [F]
      rw [map_add,map_smul,hv,smul_eq_mul,mul_one]
      ring
    have na : N a = 0 := ((hlevel a ha).self_of_nhds).mp ha
    have cn := hN.contDiffAt (hw.mem_nhds (hsub ha))
    have cF : ContDiffAt ℝ 1 F a := contDiffAt_id.add ((cn.sub L.contDiff.contDiffAt).smul contDiffAt_const)
    have derivN : HasFDerivAt N L a := (cn.differentiableAt one_ne_zero).hasFDerivAt
    let A := ContinuousLinearEquiv.refl ℝ X
    have eqD : HasFDerivAt F (A : X →L[ℝ] X) a := by
      have dF := (hasFDerivAt_id a).add ((derivN.sub L.hasFDerivAt).smul_const v)
      apply dF.congr_fderiv
      ext z
      simp [A]
    let E := cF.toOpenPartialHomeomorph F eqD one_ne_zero
    have sa : a ∈ E.source := cF.mem_toOpenPartialHomeomorph_source eqD one_ne_zero
    have ta : F a ∈ E.target := E.map_source sa
    have inva : E.symm (F a)=a := E.left_inv sa
    have ce : ContDiffAt ℝ 1 (E.symm : X → X) (F a) := cF.to_localInverse eqD one_ne_zero
    have te : Tendsto E.symm (𝓝 (F a)) (𝓝 a) := by
      have res := ce.continuousAt.tendsto
      rwa [inva] at res
    have ev : ∀ᶠ t in 𝓝 (F a), t ∈ E.target ∧ ContDiffAt ℝ 1 (E.symm : X → X) t ∧
        E.symm t ∈ W ∧ (E.symm t ∈ S ↔ N (E.symm t)=0) := by
      filter_upwards [E.open_target.mem_nhds ta,ce.eventually (by decide),
        te (hw.mem_nhds (hsub ha)),te.eventually (hlevel a ha)] with y yt yd yw ys
      exact ⟨yt,yd,yw,ys⟩
    obtain ⟨r,rp,ball⟩ := Metric.mem_nhds_iff.mp ev
    let K := Metric.ball (F a) r ∩ (L.ker : Set X)
    have cv : Convex ℝ K := (convex_ball _ _).inter L.ker.convex
    have pre (y : X) (hy : y ∈ K) : E.symm y ∈ S := by
      obtain ⟨yt,yd,yw,ys⟩ := ball hy.1
      apply ys.mpr
      have e : F (E.symm y)=y := E.right_inv yt
      rw [← lev,e]
      exact hy.2
    have dz (y : X) (hy : y ∈ K) : HasFDerivAt (fun t => f (E.symm t)) (0 : X →L[ℝ] ℝ) y := by
      obtain ⟨yt,yd,yw,ys⟩ := ball hy.1
      have d₁ := (hf.differentiableAt (hw.mem_nhds yw)).hasFDerivAt
      rw [hzero _ (pre y hy)] at d₁
      simpa only [Function.comp_def,ContinuousLinearMap.zero_comp] using d₁.comp y (yd.differentiableAt one_ne_zero).hasFDerivAt
    have ka : F a ∈ K := ⟨Metric.mem_ball_self rp,(lev a).trans na⟩
    have cf := cF.continuousAt
    filter_upwards [E.open_source.mem_nhds sa,cf.tendsto (Metric.ball_mem_nhds (F a) rp),hlevel a ha]
      with y yes yb lzero
    intro ys
    have ky : F y ∈ K := ⟨yb,(lev y).trans (lzero.mp ys)⟩
    have m := cv.norm_image_sub_le_of_norm_hasFDerivWithin_le (C:=0)
      (fun t ht => (dz t ht).hasFDerivWithinAt) (fun _ _ => by simp) ky ka
    have eq : f (E.symm (F y)) = f (E.symm (F a)) := by
      have m0 : ‖f (E.symm (F a)) - f (E.symm (F y))‖ ≤ 0 := by simpa only [zero_mul] using m
      exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm m0 (norm_nonneg _)))).symm
    have ey : E.symm (F y)=y := E.left_inv yes
    rwa [ey,inva] at eq
  letI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hs.isPreconnected
  have locally : IsLocallyConstant (fun y : S => f y.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro y
    have ev := (continuous_subtype_val.continuousAt (x:=y)).tendsto.eventually (local_eq y y.property)
    exact ev.mono fun z h => h z.property
  intro x hx y hy
  exact locally.apply_eq_of_preconnectedSpace ⟨x,hx⟩ ⟨y,hy⟩
