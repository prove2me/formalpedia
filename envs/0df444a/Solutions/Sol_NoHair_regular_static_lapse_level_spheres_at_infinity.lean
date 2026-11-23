-- Prove2me | solution 1 for NoHair.regular_static_lapse_level_spheres_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:17:54.578921+00:00
-- url     : https://prove2.me/submissions/c6794b7f-724b-4cf2-8de0-ab006322ef56

import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Theorems.Thm_NoHair_regular_static_radial_lapse_derivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint

private lemma norm_ray (n : ADMSphere) {r : ℝ} (hr : 0≤r) : ‖r • (n:X)‖=r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,mem_sphere_zero_iff_norm.mp n.property,mul_one]

private lemma large {P : X → Prop} (h : ∀ᶠ x in cocompact X,P x) : ∃ B : ℝ,∀ x : X,B≤‖x‖ → P x := by
  rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop,eventually_comap,eventually_atTop] at h
  obtain ⟨B,hB⟩:=h
  exact ⟨B,fun x hx => hB ‖x‖ hx x rfl⟩

private lemma limit_one {N : X → ℝ} {μ : ℝ} (hm : HasStaticLapseMonopole N μ) :
    Tendsto N (cocompact X) (𝓝 1) := by
  have hd := (show Tendsto (fun x : X => ‖x‖*(1-N x)) (cocompact X) (𝓝 μ) from hm).div_atTop
    (tendsto_norm_cocompact_atTop (E:=X))
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub hd
  rw [sub_zero] at ht
  apply ht.congr'
  filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop 0] with x hx
  change 1-‖x‖*(1-N x)/‖x‖=N x
  field_simp [hx.ne']
  <;> ring

private lemma far_smooth {Ω W : Set X} {N : X → ℝ} {h : X → Matrix (Fin 3) (Fin 3) ℝ}
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ᶠ x in cocompact X,x∈Ω ∧ ContDiffAt ℝ ∞ N x := by
  obtain ⟨B,hB,hd⟩:=c.compactComplement.isBounded.exists_pos_norm_lt
  filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop B] with x hx
  have ho : x∈Ω := by
    by_contra hn
    exact (not_lt_of_ge hx.le) (hd x hn)
  exact ⟨ho,c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (c.extendsAcross (subset_closure ho)))⟩

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ R L : ℝ, 0 < R ∧ 0 < L ∧ L < 1 ∧
      (∀ x : ADMPoint, R ≤ ‖x‖ → 0 < N x ∧ N x < 1 ∧ 0 < fderiv ℝ N x x) ∧
      (∀ n : ADMSphere, StrictMonoOn (fun r : ℝ => N (r • (n:ADMPoint))) (Ici R)) ∧
      ∀ n : ADMSphere, ∀ t : ℝ, L < t → t < 1 →
        ∃! r : ℝ, R < r ∧ N (r • (n:ADMPoint)) = t := by
  obtain ⟨μ,hμ,hm⟩:=regular_static_lapse_positive_monopole Ω W N h c
  have hd:=regular_static_radial_lapse_derivative Ω W N h c μ hm
  have hmu : Tendsto (fun x : X => ‖x‖*(1-N x)) (cocompact X) (𝓝 μ) := hm
  have nlim:=limit_one hm
  have ev : ∀ᶠ x in cocompact X, 0<N x ∧ μ/2<‖x‖*(1-N x) ∧
      0<‖x‖*fderiv ℝ N x x ∧ ContDiffAt ℝ ∞ N x := by
    filter_upwards [nlim.eventually_const_lt zero_lt_one, hmu.eventually_const_lt (show μ/2<μ by linarith),
      hd.eventually_const_lt hμ,far_smooth c] with x hn hm' hd' hs
    exact ⟨hn,hm',hd',hs.2⟩
  obtain ⟨B,hB⟩:=large ev
  let R:=max B 1
  let L:=max (1/2:ℝ) (1-μ/(2*R))
  have rp : 0<R := zero_lt_one.trans_le (le_max_right _ _)
  have lp : 0<L := (by norm_num : (0:ℝ)<1/2).trans_le (le_max_left _ _)
  have muR : 0<μ/(2*R) := by positivity
  have lu : L<1 := max_lt (by norm_num) (by linarith)
  have all {x : X} (hx : R≤‖x‖) := hB x ((le_max_left B 1).trans hx)
  have vals {x : X} (hx : R≤‖x‖) : 0<N x ∧ N x<1 ∧ 0<fderiv ℝ N x x := by
    obtain ⟨v,b,d,_⟩:=all hx
    have hpos : 0<1-N x := pos_of_mul_pos_right ((by linarith : 0<μ/2).trans b) (norm_nonneg _)
    exact ⟨v,by linarith,pos_of_mul_pos_right d (norm_nonneg _)⟩
  have derivative (n : ADMSphere) {r : ℝ} (hr : R≤r) :
      HasDerivAt (fun s : ℝ => N (s • (n:X))) (fderiv ℝ N (r • (n:X)) (n:X)) r := by
    have mem : R≤‖r • (n:X)‖ := by simpa only [norm_ray n (rp.le.trans hr)] using hr
    have lin : HasDerivAt (fun s : ℝ => s • (n:X)) (n:X) r := by simpa only [one_smul,id_eq] using (hasDerivAt_id r).smul_const (n:X)
    exact ((all mem).2.2.2.differentiableAt (by simp : (∞:ℕ∞ω)≠0)).hasFDerivAt.comp_hasDerivAt r lin
  have con (n : ADMSphere) : ContinuousOn (fun r : ℝ => N (r • (n:X))) (Ici R) :=
    fun r hr => (derivative n hr).continuousAt.continuousWithinAt
  have mono (n : ADMSphere) : StrictMonoOn (fun r : ℝ => N (r • (n:X))) (Ici R) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (con n)
    intro r hr
    have hb : R≤r := interior_subset hr
    rw [(derivative n hb).deriv]
    have v:=(vals (x:=r • (n:X)) (by simpa only [norm_ray n (rp.le.trans hb)] using hb)).2.2
    rw [map_smul,smul_eq_mul] at v
    exact pos_of_mul_pos_right v (rp.le.trans hb)
  refine ⟨R,L,rp,lp,lu,fun x hx => vals hx,mono,?_⟩
  intro n t ht ht1
  have hrN := (all (x:=R • (n:X)) (by rw [norm_ray n rp.le])).2.1
  rw [norm_ray n rp.le] at hrN
  have base : N (R • (n:X)) < t := by
    have e : μ/(2*R)<1-N (R • (n:X)) := by apply (div_lt_iff₀ (by positivity)).2; linarith only [hrN]
    linarith only [e,((le_max_right (1/2:ℝ) (1-μ/(2*R))).trans_lt ht)]
  have ray : Tendsto (fun r : ℝ => r • (n:X)) atTop (cocompact X) := by
    rw [←Metric.cobounded_eq_cocompact,←tendsto_norm_atTop_iff_cobounded]
    exact tendsto_id.congr' ((eventually_ge_atTop (0:ℝ)).mono (fun _ hr => (norm_ray n hr).symm))
  have up : ∀ᶠ r : ℝ in atTop, t<N (r • (n:X)) := (nlim.comp ray).eventually_const_lt ht1
  obtain ⟨q,hq,hqt⟩:=((eventually_gt_atTop R).and up).exists
  obtain ⟨r,hr,hrN⟩:=intermediate_value_Icc hq.le ((con n).mono (fun _ hx => hx.1)) (show t∈Icc _ _ from ⟨base.le,hqt.le⟩)
  have rR : R<r := lt_of_le_of_ne hr.1 (by rintro rfl; exact base.ne hrN)
  exact ⟨r,⟨rR,hrN⟩,fun s hs => (mono n).injOn hs.1.le rR.le (hs.2.trans hrN.symm)⟩
