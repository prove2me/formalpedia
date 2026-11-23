-- Prove2me | solution 1 for NoHair.static_harmonic_lapse_positive_conserved_flux
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:06:54.157975+00:00
-- url     : https://prove2.me/submissions/cb78fe66-73d5-441f-9c55-6665e1104a85

import Theorems.Thm_EuclideanSpace_integral_divergence_ball_three
import Theorems.Thm_NoHair_spatial_laplacian_in_divergence_form
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open scoped Matrix

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev bvec (i : I) : X := EuclideanSpace.single i 1

private lemma sm_pd {f : X → ℝ} {x : X} (c : ContDiffAt ℝ ∞ f x) (i : I) :
    ContDiffAt ℝ ∞ (pd i f) x :=
  (c.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

private lemma sm_inv {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a b : I) :
    ContDiffAt ℝ ∞ (fun y => (h y)⁻¹ a b) x := by
  classical
  have detS {ι : Type} [Fintype ι] [DecidableEq ι] (G : X → Matrix ι ι ℝ)
      (cG : ∀ k m, ContDiffAt ℝ ∞ (fun y => G y k m) x) :
      ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
    simp_rw [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    have pr (t : Finset ι) : ContDiffAt ℝ ∞ (fun y => ∏ j ∈ t, G y (σ j) j) x := by
      induction t using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (1:ℝ)) x)
      | @insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (cG _ _).mul ih
    exact contDiffAt_const.mul (pr Finset.univ)
  have det0 := ((h x).isUnit_iff_isUnit_det.mp hp.isUnit).ne_zero
  have adj : ContDiffAt ℝ ∞ (fun y => (h y).adjugate a b) x := by
    simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    exact contDiffAt_const.mul (detS (ι:=Fin 2) (fun y => (h y).submatrix b.succAbove a.succAbove)
      (fun k m => hc _ _))
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((detS (ι:=I) h hc).inv det0).mul adj

private lemma sm_ch {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a i j : I) :
    ContDiffAt ℝ ∞ (fun y => spatialLeviCivita h y a i j) x :=
  contDiffAt_const.mul (ContDiffAt.sum fun l _ => (sm_inv hp hc a l).mul
    (((sm_pd (hc l j) i).add (sm_pd (hc l i) j)).sub (sm_pd (hc i j) l)))

private lemma sm_grad {h : X → Mat} {N : X → ℝ} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (cn : ContDiffAt ℝ ∞ N x) (a : I) :
    ContDiffAt ℝ ∞ (staticRaisedGradient N h a) x :=
  ContDiffAt.sum fun j _ => (sm_inv hp hc a j).mul (sm_pd cn j)

private lemma sym_h {h : X → Mat} {W : Set X} (ow : IsOpen W)
    (hp : ∀ y ∈ W, (h y).PosDef) {x : X} (hx : x ∈ W) (i j k : I) :
    pd i (fun y => h y j k) x = pd i (fun y => h y k j) x := by
  have ev : (fun y => h y j k) =ᶠ[𝓝 x] (fun y => h y k j) := (show ∀ᶠ y in 𝓝 x, y ∈ W from ow.mem_nhds hx).mono
    (fun y hy => by simpa only [star_trivial] using (hp y hy).isHermitian.apply k j)
  exact congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.fderiv_eq

private lemma pd_sum {f : I → X → ℝ} {x : X} (df : ∀ j, DifferentiableAt ℝ (f j) x) (i : I) :
    pd i (fun y => ∑ j, f j y) x = ∑ j, pd i (f j) x := by
  unfold pd spatialADMPartial
  rw [fderiv_fun_sum (fun j _ => df j)]
  simp

private lemma pd_mul {f g : X → ℝ} {x : X} (df : DifferentiableAt ℝ f x) (dg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y*g y) x = pd i f x*g x + f x*pd i g x := by
  have v := (df.hasFDerivAt.mul dg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y*g y) x = _ at v
  unfold pd spatialADMPartial
  rw [v]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring
open Metric MeasureTheory

private lemma choose_lapse_cutoff (n : ℝ) (n0 : 0<n) (nq : n<1/4) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ t, 0 ≤ deriv η t) ∧ 0<deriv η n ∧
      (∀ t, t<n/2 → η t=0) ∧ (∀ t, 1/2<t → η t=1) := by
  have smooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨a,ha,slope⟩ := exists_deriv_eq_slope Real.smoothTransition zero_lt_one
    smooth.continuous.continuousOn (smooth.differentiable (by simp)).differentiableOn
  have slope' : deriv Real.smoothTransition a=1 := by simpa using slope
  let e := n/2
  have ep : 0<e := half_pos n0
  let t := fun s : ℝ => a + (s-n)/e
  let η := Real.smoothTransition ∘ t
  have st : ContDiff ℝ ∞ t := contDiff_const.add ((contDiff_id.sub contDiff_const).div_const _)
  have ht : t n=a := by simp [t]
  have mono : Monotone η := Real.smoothTransition.monotone.comp (fun u v h => by
    dsimp only [t]; gcongr)
  refine ⟨η,smooth.comp st,fun _ => mono.deriv_nonneg,?_,?_,?_⟩
  · have td : HasDerivAt t (1/e) n := ((hasDerivAt_id n).sub_const n).div_const e |>.const_add a
    have d := ((smooth.differentiable (by simp) (t n)).hasDerivAt.comp n td).deriv
    change deriv η n = deriv Real.smoothTransition (t n) * (1/e) at d
    rw [d,ht,slope',one_mul]
    positivity
  · intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    change a + (x-n)/e ≤ 0
    have le : (x-n)/e ≤ -1 := (div_le_iff₀ ep).mpr (by dsimp only [e]; linarith only [hx])
    linarith only [le,ha.2]
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    change 1 ≤ a + (x-n)/e
    have le : 1 ≤ (x-n)/e := (le_div_iff₀ ep).mpr (by dsimp only [e]; linarith only [hx,nq])
    linarith only [le,ha.1]

set_option maxHeartbeats 850000 in
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ m R : ℝ, 0 < m ∧ 0 < R ∧ ∀ r : ℝ, R < r →
      r^2 * (∫ n : ADMSphere, ∑ i : Fin 3,
        (Real.sqrt (h (r • (n:ADMPoint))).det * staticRaisedGradient N h i (r • (n:ADMPoint))) *
          (n:ADMPoint) i ∂admSurfaceMeasure) = m := by
  classical
  let vol := fun x : X => Real.sqrt (h x).det
  let A := fun (i : I) (x : X) => vol x * staticRaisedGradient N h i x
  let E := staticLapseGradientSq N h
  have hW : Ω ⊆ W := subset_closure.trans c.extendsAcross
  have cn {x:X} (hx : x∈W) := c.smoothLapse.contDiffAt (c.openExtension.mem_nhds hx)
  have ch {x:X} (hx : x∈W) (i j : I) := (c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds hx)
  have cv {x:X} (hx : x∈W) : ContDiffAt ℝ ∞ vol x := by
    have sd : ContDiffAt ℝ ∞ (fun y => (h y).det) x := by
      simp_rw [Matrix.det_fin_three]
      have entry := ch hx
      fun_prop
    exact sd.sqrt (c.positiveMetric x hx).det_pos.ne'
  have ca {x:X} (hx : x∈W) (i : I) : ContDiffAt ℝ ∞ (A i) x :=
    (cv hx).mul (sm_grad (c.positiveMetric x hx) (ch hx) (cn hx) i)
  have ce {x:X} (hx : x∈W) : ContDiffAt ℝ ∞ E x :=
    ContDiffAt.sum fun i _ => (sm_pd (cn hx) i).mul (sm_grad (c.positiveMetric x hx) (ch hx) (cn hx) i)
  obtain ⟨b,hb⟩ := c.hasBoundary
  have bw := c.extendsAcross (frontier_subset_closure hb)
  obtain ⟨κ,kp,kval⟩ := c.horizon
  have eb : 0 < E b := by change 0 < staticLapseGradientSq N h b; rw [(kval b hb).2.1]; positivity
  have en : ∀ᶠ x in 𝓝 b, 0<E x := (ce bw).continuousAt.tendsto (isOpen_Ioi.mem_nhds eb)
  have nb : N b < 1/4 := by rw [(c.regularLevel b hb).1]; norm_num
  have nn : ∀ᶠ x in 𝓝 b, N x<1/4 := (cn bw).continuousAt.tendsto (isOpen_Iio.mem_nhds nb)
  obtain ⟨w,hw,hwe,hwn⟩ := ((mem_closure_iff_frequently.mp (frontier_subset_closure hb)).and_eventually (en.and nn)).exists
  have wp : 0<N w := (c.positiveSide w (hW hw)).mp hw
  obtain ⟨η,cη,nonneg,strict,low,high⟩ := choose_lapse_cutoff (N w) wp hwn
  let B := fun (i:I) (x:X) => if x∈Ω then η (N x)*A i x else 0
  have inside (i : I) {x:X} (hx : x∈Ω) : B i =ᶠ[𝓝 x] (fun y => η (N y)*A i y) :=
    (show ∀ᶠ y in 𝓝 x, y∈Ω from c.openSlice.mem_nhds hx).mono fun y hy => if_pos hy
  have outside (i : I) {x:X} (hx : x∉Ω) : B i =ᶠ[𝓝 x] (fun _ => 0) := by
    by_cases hc : x∈closure Ω
    · have fr : x∈frontier Ω := by rw [frontier,c.openSlice.interior_eq]; exact ⟨hc,hx⟩
      have ns : N x < N w/2 := by rw [(c.regularLevel x fr).1]; exact half_pos wp
      have ev : ∀ᶠ y in 𝓝 x, N y < N w/2 := (cn (c.extendsAcross hc)).continuousAt.tendsto (isOpen_Iio.mem_nhds ns)
      exact ev.mono fun y hy => by simp only [B,low _ hy,zero_mul,ite_self]
    · exact (show ∀ᶠ y in 𝓝 x, y∉closure Ω from isClosed_closure.isOpen_compl.mem_nhds hc).mono fun y hy =>
        if_neg (fun h => hy (subset_closure h))
  have cb (i:I) : ContDiff ℝ ∞ (B i) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x∈Ω
    · exact (((cη.contDiffAt.comp x (cn (hW hx))).mul (ca (hW hx) i))).congr_of_eventuallyEq (inside i hx)
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (0:ℝ)) x).congr_of_eventuallyEq (outside i hx)
  let div := fun x : X => ∑ i : I, pd i (B i) x
  have cd : ContDiff ℝ ∞ div :=
    ContDiff.sum fun i _ => ((cb i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have din {x:X} (hx : x∈Ω) : div x=deriv η (N x)*vol x*E x := by
    have wx := hW hx
    have hd := spatial_laplacian_in_divergence_form N h W c.openExtension c.smoothLapse c.smoothMetric c.positiveMetric x wx
    change (∑ i : I, pd i (A i) x) = vol x*_ at hd
    rw [(c.equations x (subset_closure hx)).2,mul_zero] at hd
    have dd (i:I) : pd i (fun y => η (N y)) x = deriv η (N x)*pd i N x := by
      have de := (((cη.differentiable (by simp) (N x)).hasDerivAt).comp_hasFDerivAt x ((cn wx).differentiableAt (by simp)).hasFDerivAt).fderiv
      unfold pd spatialADMPartial
      change fderiv ℝ (η ∘ N) x _ = _
      rw [de]; rfl
    have row (i:I) : pd i (B i) x = deriv η (N x)*pd i N x*A i x+η (N x)*pd i (A i) x := by
      have r := congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) (inside i hx).fderiv_eq
      change pd i (B i) x = pd i (fun y => η (N y)*A i y) x at r
      rw [r,pd_mul (f:=fun y => η (N y)) (g:=A i) ((cη.contDiffAt.comp x (cn wx)).differentiableAt (by simp))
        ((ca wx i).differentiableAt (by simp)),dd]
    change (∑ i : I, pd i (B i) x) = _
    simp only [row,Finset.sum_add_distrib,←Finset.mul_sum,hd,mul_zero,add_zero]
    simp only [A,E,staticLapseGradientSq,Fin.sum_univ_three,pd]
    ring
  have dout {x:X} (hx : x∉Ω) : div x=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have d : fderiv ℝ (B i) x = fderiv ℝ (fun _ : X => (0:ℝ)) x := (outside i hx).fderiv_eq
    change fderiv ℝ (B i) x (bvec i)=0
    rw [d,fderiv_const_apply]; rfl
  have epos {x:X} (hx : x∈Ω) : 0 ≤ E x := by
    let n := fun i : I => pd i N x
    have pe := (c.positiveMetric x (hW hx)).inv.posSemidef.dotProduct_mulVec_nonneg n
    simpa only [E,n,staticLapseGradientSq,staticRaisedGradient,pd,dotProduct,Matrix.mulVec,star_trivial] using pe
  have dn : 0≤div := by
    intro x
    by_cases hx : x∈Ω
    · rw [din hx]; exact mul_nonneg (mul_nonneg (nonneg _) (Real.sqrt_nonneg _)) (epos hx)
    · rw [dout hx]; rfl
  have dw : 0<div w := by
    rw [din hw]
    exact mul_pos (mul_pos strict (Real.sqrt_pos.mpr (c.positiveMetric w (hW hw)).det_pos)) hwe
  obtain ⟨R₀,C,rp,cp,fall⟩ := c.falloff 0
  obtain ⟨K,kb⟩ := c.compactComplement.isBounded.exists_norm_le
  let R := max R₀ (max K (4*C))
  have rp' : 0<R := rp.trans_le (le_max_left _ _)
  have far (x:X) (hx:R<‖x‖) : x∈Ω ∧ 1/2<N x := by
    have hxr := max_lt_iff.mp hx
    have hv := max_lt_iff.mp hxr.2
    have hr := rp.trans hxr.1
    have err := (fall x hxr.1).1
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at err
    have small : C/‖x‖≤1/4 := (div_le_iff₀ hr).mpr (by linarith only [hv.2])
    exact ⟨by by_contra hn; exact hv.1.not_ge (kb x hn),by linarith only [(abs_le.mp err).1,small]⟩
  have dz (x:X) (hx:R<‖x‖) : div x=0 := by
    obtain ⟨ho,hn⟩ := far x hx
    have eq : η =ᶠ[𝓝 (N x)] (fun _ => 1) := (show ∀ᶠ t in 𝓝 (N x), 1/2<t from isOpen_Ioi.mem_nhds hn).mono high
    rw [din ho,eq.deriv_eq,deriv_const,zero_mul,zero_mul]
  have support : HasCompactSupport div := HasCompactSupport.intro' (isCompact_closedBall (0:X) R) Metric.isClosed_closedBall
    (fun x hx => dz x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx))
  let F := fun x : X => WithLp.toLp 2 (fun i : I => B i x)
  have cf : ContDiff ℝ ∞ F := PiLp.contDiff_toLp.comp (contDiff_pi.mpr cb)
  have dF (x : X) : (∑ i : I, (fderiv ℝ F x (bvec i)) i) = div x := by
    apply Finset.sum_congr rfl
    intro i _
    let proj : X →L[ℝ] ℝ := PiLp.proj 2 (fun _ : I => ℝ) i
    have eq := (proj.hasFDerivAt.comp x (cf.differentiable (by simp) x).hasFDerivAt).fderiv
    change fderiv ℝ (B i) x = proj.comp (fderiv ℝ F x) at eq
    exact (congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) eq).symm
  refine ⟨∫ x, div x, R, cd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero support dn dw.ne', rp',?_⟩
  intro r hr
  have rp'' := rp'.trans hr
  have stokes := EuclideanSpace.integral_divergence_ball_three F (cf.of_le (by simp)) r rp''
  simp_rw [show ∀ x : X, (∑ i : I, (fderiv ℝ F x (EuclideanSpace.single i (1:ℝ))) i) = div x from dF] at stokes
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => dz x (hr.trans_le
    (le_of_not_gt (fun h => hx (Metric.mem_ball.mpr (by simpa only [dist_zero_right] using h))))))] at stokes
  rw [stokes]
  apply congrArg (fun s : ℝ => r^2*s)
  apply integral_congr_ae
  filter_upwards with n
  have unit : ‖(n:X)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have nr : ‖r • (n:X)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos rp'',unit,mul_one]
  obtain ⟨ho,hn⟩ := far (r • (n:X)) (by rwa [nr])
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,F,WithLp.ofLp_toLp,B,if_pos ho,high _ hn,one_mul,A,vol,mul_comm]
