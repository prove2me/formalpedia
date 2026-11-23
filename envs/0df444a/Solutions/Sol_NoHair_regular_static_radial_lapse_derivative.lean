-- Prove2me | solution 1 for NoHair.regular_static_radial_lapse_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:23:52.901176+00:00
-- url     : https://prove2.me/submissions/99a37e00-1336-491d-a575-3159a13270d4

import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Mathlib.Analysis.Calculus.Deriv.MeanValue
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint

private lemma slope_error {F G H : ℝ → ℝ} {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (d : ∀ s ∈ Icc 0 t, HasDerivAt F (G s) s ∧ HasDerivAt G (H s) s ∧ |H s|≤C) :
    |G 0-(F t-F 0)/t| ≤ C*t := by
  obtain ⟨b,hb,eq⟩:=exists_hasDerivAt_eq_slope F G ht
    (fun s hs => (d s hs).1.continuousAt.continuousWithinAt) (fun s hs => (d s (Ioo_subset_Icc_self hs)).1)
  rw [sub_zero] at eq
  have sub : Icc 0 b ⊆ Icc 0 t := Icc_subset_Icc le_rfl hb.2.le
  obtain ⟨a,ha,eq'⟩:=exists_hasDerivAt_eq_slope G H hb.1
    (fun s hs => (d s (sub hs)).2.1.continuousAt.continuousWithinAt)
    (fun s hs => (d s (sub (Ioo_subset_Icc_self hs))).2.1)
  rw [sub_zero] at eq'
  have v:=(eq_div_iff hb.1.ne').mp eq'
  rw [←eq,abs_sub_comm,←v,abs_mul,abs_of_pos hb.1]
  exact mul_le_mul (d a (sub (Ioo_subset_Icc_self ha))).2.2 hb.2.le hb.1.le hC

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (μ : ℝ) (hm : HasStaticLapseMonopole N μ) :
    Tendsto (fun x : ADMPoint => ‖x‖ * fderiv ℝ N x x) (cocompact ADMPoint) (𝓝 μ) := by
  obtain ⟨B,hB,hout⟩:=c.compactComplement.isBounded.exists_pos_norm_lt
  have sm {x : X} (hx : B<‖x‖) : ContDiffAt ℝ ∞ N x := by
    apply c.smoothLapse.contDiffAt
    apply c.openExtension.mem_nhds
    apply c.extendsAcross
    apply subset_closure
    by_contra hn
    exact (not_lt_of_ge hx.le) (hout x hn)
  obtain ⟨R,C,hR,hC,bd⟩:=c.falloff 2
  have dd {z : X} (hz : R<‖z‖) : ‖fderiv ℝ (fderiv ℝ N) z‖ ≤ C/‖z‖^3 := by
    have eq:=norm_iteratedFDeriv_fderiv (𝕜:=ℝ) (f:=fun y : X => N y-1) (x:=z) (n:=1)
    have hh : (fderiv ℝ (fun y : X => N y-1))=fderiv ℝ N := funext (fun _ => fderiv_sub_const 1)
    rw [hh,norm_iteratedFDeriv_one] at eq
    exact eq.trans_le (bd z hz).1
  let F := fun (x : X) (t : ℝ) => ‖x‖*(N ((1+t) • x)-1)
  let G := fun (x : X) (t : ℝ) => ‖x‖*fderiv ℝ N ((1+t) • x) x
  let H := fun (x : X) (t : ℝ) => ‖x‖*fderiv ℝ (fderiv ℝ N) ((1+t) • x) x x
  have Ft {t : ℝ} (ht : 0≤t) : Tendsto (fun x : X => F x t) (cocompact X) (𝓝 (-μ/(1+t))) := by
    have hp : 0<1+t := by linarith
    have go : Tendsto (fun x : X => (1+t) • x) (cocompact X) (cocompact X) := by
      rw [←Metric.cobounded_eq_cocompact,←tendsto_norm_atTop_iff_cobounded]
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hp,Metric.cobounded_eq_cocompact]
        using (tendsto_norm_cocompact_atTop (E:=X)).const_mul_atTop hp
    have b := ((show Tendsto (fun x : X => ‖x‖*(1-N x)) (cocompact X) (𝓝 μ) from hm).comp go).neg.div_const (1+t)
    apply b.congr'
    apply Eventually.of_forall
    intro x
    change -(‖(1+t) • x‖*(1-N ((1+t) • x)))/(1+t)=_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hp]
    dsimp only [F]
    field_simp [hp.ne']
    <;> ring
  have err (x : X) (hx : max B R < ‖x‖) (t : ℝ) (ht : 0<t) :
      |G x 0-(F x t-F x 0)/t|≤C*t := by
    obtain ⟨xb,xr⟩:=max_lt_iff.mp hx
    have xp:=hR.trans xr
    apply slope_error (H:=H x) ht hC.le
    intro s hs
    let z:=(1+s) • x
    have sp : 0<1+s := by linarith [hs.1]
    have nz : ‖z‖=(1+s)*‖x‖ := by simp [z,norm_smul,Real.norm_eq_abs,abs_of_pos sp]
    have zx : ‖x‖≤‖z‖ := by rw [nz]; nlinarith only [mul_nonneg hs.1 xp.le]
    have cn:=sm (xb.trans_le zx)
    have lin : HasDerivAt (fun a : ℝ => (1+a) • x) x s := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id s).const_add 1).smul_const x
    have dN:=cn.differentiableAt (by simp : (∞:ℕ∞ω)≠0)
    have dDN:=(cn.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp : (∞:ℕ∞ω)≠0)
    refine ⟨((dN.hasFDerivAt.comp_hasDerivAt s lin).sub_const 1).const_mul _,?_,?_⟩
    · let ev : (X →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ x
      exact (ev.hasFDerivAt.comp_hasDerivAt s (dDN.hasFDerivAt.comp_hasDerivAt s lin)).const_mul _
    · have le1 := (fderiv ℝ (fderiv ℝ N) z x).le_opNorm x
      have le2 := (fderiv ℝ (fderiv ℝ N) z).le_opNorm x
      have le3 := (le_div_iff₀ (pow_pos (xp.trans_le zx) 3)).mp (dd (xr.trans_le zx))
      have powb:=pow_le_pow_left₀ xp.le zx 3
      change |‖x‖ * fderiv ℝ (fderiv ℝ N) z x x|≤C
      rw [abs_mul,abs_of_nonneg (norm_nonneg x)]
      calc
        _ ≤ ‖x‖ * ((‖fderiv ℝ (fderiv ℝ N) z‖*‖x‖)*‖x‖) :=
          mul_le_mul_of_nonneg_left (le1.trans (mul_le_mul_of_nonneg_right le2 xp.le)) xp.le
        _ = ‖fderiv ℝ (fderiv ℝ N) z‖*‖x‖^3 := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left powb (norm_nonneg (fderiv ℝ (fderiv ℝ N) z))).trans le3
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let t := ε/(4*(C+|μ|+1))
  have den : 0<4*(C+|μ|+1) := by positivity
  have ht : 0<t := div_pos he den
  have ht' : 0<1+t := by linarith
  have small : (C+|μ|)*t < ε/2 := by
    have te : 4*(C+|μ|+1)*t=ε := by dsimp only [t]; field_simp
    nlinarith only [te,ht,he]
  have sl:=((Ft ht.le).sub (Ft (t:=0) le_rfl)).div_const t
  have lim : (-μ/(1+t) - -μ/(1+(0:ℝ)))/t=μ/(1+t) := by field_simp [ht.ne',ht'.ne'] <;> ring
  rw [lim] at sl
  have gap : |μ/(1+t)-μ| ≤ |μ| *t := by
    rw [show μ/(1+t)-μ=-(μ*t)/(1+t) by field_simp [ht'.ne'] <;> ring,abs_div,abs_neg,abs_mul,abs_of_pos ht,abs_of_pos ht']
    apply (div_le_iff₀ ht').2
    nlinarith only [mul_nonneg (abs_nonneg μ) (sq_nonneg t)]
  filter_upwards [Metric.tendsto_nhds.mp sl (ε/2) (by positivity),
    (tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop (max B R)] with x hs hx
  let slope := (F x t-F x 0)/t
  change dist slope (μ/(1+t))<ε/2 at hs
  have base : G x 0=‖x‖*fderiv ℝ N x x := by simp [G]
  rw [←base]
  calc
    dist (G x 0) μ ≤ dist (G x 0) slope + dist slope (μ/(1+t)) + dist (μ/(1+t)) μ :=
      (dist_triangle (G x 0) (μ/(1+t)) μ).trans (add_le_add (dist_triangle (G x 0) slope (μ/(1+t))) le_rfl)
    _ < ε := by
      have one : dist (G x 0) slope≤C*t := err x hx t ht
      have two : dist (μ/(1+t)) μ≤|μ| *t := gap
      linarith only [one,two,hs,small,show (C+|μ|)*t=C*t+|μ| *t by ring]
