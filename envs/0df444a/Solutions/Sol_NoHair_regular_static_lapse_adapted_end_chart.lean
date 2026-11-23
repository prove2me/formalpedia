-- Prove2me | solution 1 for NoHair.regular_static_lapse_adapted_end_chart
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:35:13.21847+00:00
-- url     : https://prove2.me/submissions/978b25f9-42e8-4328-a6bd-d259a6224681

import Theorems.Thm_NoHair_regular_static_lapse_level_spheres_at_infinity
import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Theorems.Thm_NoHair_diffeomorphism_of_bijective_radial_scale
import Mathlib.Analysis.InnerProductSpace.Calculus
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint

private lemma norm_ray (n : ADMSphere) {r : ℝ} (hr : 0 ≤ r) : ‖r • (n:X)‖=r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,mem_sphere_zero_iff_norm.mp n.property,mul_one]

private lemma large {P : X → Prop} (h : ∀ᶠ x in cocompact X,P x) : ∃ B : ℝ,∀ x : X,B ≤ ‖x‖ → P x := by
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

private noncomputable def wgt (s : ℝ) := (1-s)/(1+s)
private lemma wpos {s : ℝ} (h : 0 ≤ s) (hs : s < 1) : 0<wgt s :=
  div_pos (sub_pos.mpr hs) (by linarith)
private lemma wdec {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : wgt t < wgt s := by
  apply (div_lt_div_iff₀ (by linarith : 0<1+t) (by linarith : 0<1+s)).2
  nlinarith only [hst]
private lemma winv {s : ℝ} (hs : 0 ≤ s) : wgt (wgt s)=s := by
  have hp : 1+s ≠ 0 := by linarith
  have hsum : 1+wgt s=2/(1+s) := by dsimp [wgt]; field_simp <;> ring
  change (1-wgt s)/(1+wgt s)=s
  rw [hsum]
  dsimp only [wgt]
  field_simp [hp] <;> ring
private lemma dw {s : ℝ} (hs : 0 ≤ s) : HasDerivAt wgt (-2/(1+s)^2) s := by
  have hr : 1+s ≠ 0 := by linarith
  have a := ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div ((hasDerivAt_id s).const_add 1) hr
  have eq : -2/(1+s)^2=((0-1)*(1+s)-(1-s)*1)/(1+s)^2 := by ring
  rw [eq]
  exact a

private noncomputable def rayDirection (x : X) := ‖x‖⁻¹ • x
private lemma unit_norm {x : X} (hx : 0<‖x‖) : ‖rayDirection x‖=1 := by
  rw [rayDirection,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx),inv_mul_cancel₀ hx.ne']
private lemma unit_ray {s : ℝ} (h : 0<s) (x : X) : rayDirection (s • x)=rayDirection x := by
  simp only [rayDirection,norm_smul,Real.norm_eq_abs,abs_of_pos h,mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ h.ne',mul_one]
private lemma unscale {x : X} (h : 0<‖x‖) : ‖x‖ • rayDirection x=x := by
  rw [rayDirection,smul_smul,mul_inv_cancel₀ h.ne',one_smul]

private lemma weight_derivative {N : X → ℝ} {x : X} (p : 0<‖x‖) (v : 0<N x) (v' : N x<1)
    (d : 0<fderiv ℝ N x x) (sN : ContDiffAt ℝ ∞ N x) :
    let u:=fun z : X => wgt (N z)/‖z‖
    ContDiffAt ℝ ∞ u x ∧ u x≠0 ∧ u x+fderiv ℝ u x x≠0 := by
  let u:=fun z : X => wgt (N z)/‖z‖
  have den : 0<1+N x := by linarith
  have sw : ContDiffAt ℝ ∞ (fun z => wgt (N z)) x :=
    (contDiffAt_const.sub sN).div (contDiffAt_const.add sN) den.ne'
  have su : ContDiffAt ℝ ∞ u x := sw.div (contDiffAt_norm ℝ (norm_pos_iff.mp p)) p.ne'
  refine ⟨su,(div_pos (wpos v.le v') p).ne',?_⟩
  have lin : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa only [one_smul,id_eq] using (hasDerivAt_id (1:ℝ)).smul_const x
  have chain (f : X → ℝ) (df : ContDiffAt ℝ ∞ f x) :
      HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f x x) 1 := by
    have q : DifferentiableAt ℝ f ((1:ℝ) • x) := by rw [one_smul]; exact df.differentiableAt (by simp)
    simpa only [one_smul,Function.comp_def] using (q.hasFDerivAt.comp_hasDerivAt 1 lin)
  have n1 : HasDerivAt (fun t : ℝ => N (t • x)) (fderiv ℝ N x x) 1 := chain N sN
  have u1 := (hasDerivAt_id (1:ℝ)).mul (chain u su)
  have left : HasDerivAt (fun t : ℝ => t*u (t • x)) (u x+fderiv ℝ u x x) 1 := by
    simpa only [Pi.mul_def,id_eq,one_smul,one_mul] using u1
  have ws : HasDerivAt wgt (-2/(1+N x)^2) (N ((1:ℝ) • x)) := by rw [one_smul]; exact dw v.le
  have right := ((ws.comp 1 n1).div_const ‖x‖)
  have same : (fun t : ℝ => t*u (t • x)) =ᶠ[𝓝 1] (fun t => wgt (N (t • x))/‖x‖) := by
    filter_upwards [eventually_gt_nhds (show (0:ℝ)<1 by norm_num)] with t ht
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    field_simp [ht.ne',p.ne'] <;> ring
  have eq := (left.congr_of_eventuallyEq same.symm).unique right
  change u x + fderiv ℝ u x x ≠ 0
  rw [eq]
  exact div_ne_zero (mul_ne_zero (div_ne_zero (by norm_num) (pow_ne_zero _ den.ne')) d.ne') p.ne'

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ (δ : ℝ) (e : OpenPartialHomeomorph ADMPoint ADMPoint), 0 < δ ∧
      e.source = ball 0 δ ∩ ({0} : Set ADMPoint)ᶜ ∧ e.target ⊆ Ω ∧
      (∃ R : ℝ, ∀ x : ADMPoint, R < ‖x‖ → x ∈ e.target) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      Tendsto (fun y : ADMPoint => ‖e y‖) (𝓝[≠] 0) atTop ∧
      Tendsto (fun x : ADMPoint => e.symm x) (cocompact ADMPoint) (𝓝 0) ∧
      ∀ y ∈ e.source, (1-N (e y))/(1+N (e y)) = ‖y‖ ∧
        e y = (‖e y‖/‖y‖) • y := by
  obtain ⟨R₀,L₀,r₀,l₀,l₁,values,mono,level⟩:=regular_static_lapse_level_spheres_at_infinity Ω W N h c
  obtain ⟨μ,hμ,hm⟩:=regular_static_lapse_positive_monopole Ω W N h c
  have hm' : Tendsto (fun x : X => ‖x‖*(1-N x)) (cocompact X) (𝓝 μ) := hm
  obtain ⟨B,hB⟩:=large ((far_smooth c).and (hm'.eventually_const_lt (show μ/2<μ by linarith)))
  let R:=max R₀ B
  let L:=max L₀ (1-μ/(2*R))
  have rp : 0<R := r₀.trans_le (le_max_left _ _)
  have lp : 0<L := l₀.trans_le (le_max_left _ _)
  have extra : 0 < μ/(2*R) := by positivity
  have lu : L<1 := max_lt l₁ (by linarith only [extra])
  let δ:=wgt L
  have dp : 0<δ := wpos lp.le lu
  let S:={x : X | R<‖x‖ ∧ L<N x}
  let T:=ball (0:X) δ ∩ ({0}:Set X)ᶜ
  let u:=fun x : X => wgt (N x)/‖x‖
  let F:=fun x : X => u x • x
  have sv {x : X} (hx : x∈S) := values x ((le_max_left R₀ B).trans hx.1.le)
  have sx {x : X} (hx : x∈S) := hB x ((le_max_right R₀ B).trans hx.1.le)
  have nx {x : X} (hx : x∈S) : 0<‖x‖ := rp.trans hx.1
  have pu {x : X} (hx : x∈S) : 0<u x := div_pos (wpos (sv hx).1.le (sv hx).2.1) (nx hx)
  have fsize {x : X} (hx : x∈S) : ‖F x‖=wgt (N x) := by
    change ‖u x • x‖=_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pu hx)]
    exact div_mul_cancel₀ _ (nx hx).ne'
  have fdir {x : X} (hx : x∈S) : rayDirection (F x)=rayDirection x := unit_ray (pu hx) x
  have opS : IsOpen S := by
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have ha : ∀ᶠ z : X in 𝓝 x, R<‖z‖ := (continuous_norm.tendsto x) (isOpen_Ioi.mem_nhds hx.1)
    have hb : ∀ᶠ z : X in 𝓝 x, L<N z := (sx hx).1.2.continuousAt.tendsto (isOpen_Ioi.mem_nhds hx.2)
    exact ha.and hb
  have opT : IsOpen T := isOpen_ball.inter isClosed_singleton.isOpen_compl
  have ps {y : X} (hy : y∈T) : 0<‖y‖ := norm_pos_iff.mpr (by simpa using hy.2)
  have maps : MapsTo F S T := by
    intro x hx
    have z := wpos (sv hx).1.le (sv hx).2.1
    have b : ‖F x‖<δ := (fsize hx) ▸ wdec lp.le hx.2
    exact ⟨mem_ball_zero_iff.mpr b,by simpa using (norm_pos_iff.mp ((fsize hx).symm ▸ z))⟩
  have inj : InjOn F S := by
    intro x hx z hz ez
    have ew : wgt (N x)=wgt (N z) := (fsize hx).symm.trans ((congrArg norm ez).trans (fsize hz))
    have hN := congrArg wgt ew
    rw [winv (sv hx).1.le,winv (sv hz).1.le] at hN
    have eu : rayDirection x=rayDirection z := (fdir hx).symm.trans ((congrArg rayDirection ez).trans (fdir hz))
    let n : ADMSphere := ⟨rayDirection x,mem_sphere_zero_iff_norm.mpr (unit_norm (nx hx))⟩
    have xx : ‖x‖ • (n:X)=x := unscale (nx hx)
    have zz : ‖z‖ • (n:X)=z := by change ‖z‖ • rayDirection x=z; rw [eu,unscale (nx hz)]
    have eqr : ‖x‖=‖z‖ := (mono n).injOn ((le_max_left R₀ B).trans hx.1.le)
      ((le_max_left R₀ B).trans hz.1.le) (by simpa only [xx,zz] using hN)
    exact xx.symm.trans ((congrArg (fun t : ℝ => t • (n:X)) eqr).trans zz)
  have sur : SurjOn F S T := by
    intro y hy
    let n : ADMSphere := ⟨rayDirection y,mem_sphere_zero_iff_norm.mpr (unit_norm (ps hy))⟩
    have yd := mem_ball_zero_iff.mp hy.1
    have ltL : L<wgt ‖y‖ := by simpa only [δ,winv lp.le] using wdec (ps hy).le yd
    have lt1 : wgt ‖y‖<1 := by simpa [wgt] using wdec (s:=0) le_rfl (ps hy)
    obtain ⟨r,⟨hr,hrN⟩,_⟩:=level n (wgt ‖y‖) ((le_max_left L₀ _).trans_lt ltL) lt1
    have bound := (hB (R • (n:X)) (by rw [norm_ray n rp.le]; exact le_max_right R₀ B)).2
    rw [norm_ray n rp.le] at bound
    have v : N (R • (n:X))<L := by
      have v : μ/(2*R)<1-N (R • (n:X)) := by apply (div_lt_iff₀ (by positivity)).2; linarith only [bound]
      exact (show N (R • (n:X))<1-μ/(2*R) by linarith).trans_le (le_max_right _ _)
    have rr : R<r := by
      by_contra! hs
      have a:=(mono n).monotoneOn hr.le (le_max_left R₀ B) hs
      change N (r • (n:X)) ≤ N (R • (n:X)) at a
      rw [hrN] at a
      linarith
    let x:=r • (n:X)
    have hx : x∈S := ⟨by change R<‖r • (n:X)‖; rw [norm_ray n (r₀.trans hr).le]; exact rr,hrN ▸ ltL⟩
    have ey : ‖F x‖=‖y‖ := by rw [fsize hx,show N x=wgt ‖y‖ from hrN,winv (ps hy).le]
    have dd : rayDirection (F x)=rayDirection y := by
      rw [fdir hx,show rayDirection x=rayDirection (n:X) from unit_ray (r₀.trans hr) _]
      change ‖rayDirection y‖⁻¹ • rayDirection y=rayDirection y
      rw [unit_norm (ps hy),inv_one,one_smul]
    exact ⟨x,hx,(unscale (ey.symm ▸ ps hy)).symm.trans (by rw [ey,dd,unscale (ps hy)])⟩
  obtain ⟨e,es,et,ef,efS,eiT⟩:=diffeomorphism_of_bijective_radial_scale u S T opS opT ⟨maps,inj,sur⟩
    (fun x hx => weight_derivative (nx hx) (sv hx).1 (sv hx).2.1 (sv hx).2.2 (sx hx).1.2)
  have tails : ∀ᶠ x : X in cocompact X,x∈S :=
    ((tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R).and ((limit_one hm).eventually_const_lt lu)
  have point {y : X} (hy : y∈T) : e.symm y∈S := es ▸ e.map_target (et.symm ▸ hy)
  have inv {y : X} (hy : y∈T) : F (e.symm y)=y :=
    (ef _ (point hy)).symm.trans (e.right_inv (et.symm ▸ hy))
  have size {y : X} (hy : y∈T) : wgt (N (e.symm y))=‖y‖ :=
    (fsize (point hy)).symm.trans (congrArg norm (inv hy))
  have eventuallyT : ∀ᶠ y : X in 𝓝[≠] (0:X),y∈T :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds _ dp)).and self_mem_nhdsWithin
  refine ⟨δ,e.symm,dp,et,?_,?_,?_,?_,?_,?_,?_⟩
  · change e.source ⊆ Ω
    rw [es]
    exact fun _ hx => (sx hx).1.1
  · obtain ⟨b,hb⟩:=large tails
    refine ⟨b,?_⟩
    intro x hx
    change x∈e.source
    rw [es]
    exact hb x hx.le
  · change ContDiffOn ℝ ∞ e.symm e.target
    rw [et]; exact eiT
  · change ContDiffOn ℝ ∞ e e.source
    rw [es]; exact efS
  · apply Filter.tendsto_atTop.2
    intro K
    let η:=μ/(8*(|K|+1))
    have pη : 0<η := by dsimp only [η]; positivity
    have val : 8*(|K|+1)*η=μ := by dsimp only [η]; field_simp
    filter_upwards [eventuallyT,Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds (0:X) pη)] with y hy hsmall
    have hys:=mem_ball_zero_iff.mp hsmall
    let z:=e.symm y
    have zs : z∈S := point hy
    have id : 1-N z=‖y‖*(1+N z) := (div_eq_iff (by linarith [(sv zs).1] : 1+N z≠0)).mp (size hy)
    have defect : 1-N z ≤ 2*‖y‖ := by rw [id]; nlinarith only [mul_nonneg (norm_nonneg y) (sub_nonneg.mpr (sv zs).2.1.le)]
    have b:=(sx zs).2
    by_contra! hn
    have b1 : ‖z‖ ≤ |K|+1 := (hn.le.trans (le_abs_self K)).trans (by linarith)
    have b2:=mul_le_mul b1 defect (sub_nonneg.mpr (sv zs).2.1.le) (by positivity : 0 ≤ |K|+1)
    have bb:=mul_le_mul_of_nonneg_left hys.le (by positivity : 0 ≤ |K|+1)
    nlinarith only [b,b2,bb,val,hμ]
  · have hw : Tendsto (fun x : X => wgt (N x)) (cocompact X) (𝓝 0) := by
      have cw := (dw (s:=1) zero_le_one).continuousAt.tendsto.comp (limit_one hm)
      simpa [Function.comp_def,wgt] using cw
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply hw.congr'
    filter_upwards [tails] with x hx
    change wgt (N x)=‖e x‖
    rw [ef x hx]
    exact (fsize hx).symm
  · intro y hy
    change y∈e.target at hy
    have ht : y∈T := et ▸ hy
    have xh:=point ht
    have eu : rayDirection (e.symm y)=rayDirection y := (fdir xh).symm.trans (congrArg rayDirection (inv ht))
    refine ⟨size ht,?_⟩
    calc
      _ = ‖e.symm y‖ • rayDirection (e.symm y) := (unscale (nx xh)).symm
      _ = _ := by rw [eu,rayDirection,smul_smul,div_eq_mul_inv]
