-- Prove2me | solution 2 for NoHair.regular_static_lapse_euclidean_poisson_source
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:55:24.800598+00:00
-- url     : https://prove2.me/submissions/8bf8f849-b97f-411d-9a09-da7c1f633a7a

import Theorems.Thm_EuclideanSpace_integral_divergence_ball_three
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Theorems.Thm_NoHair_static_lapse_euclidean_laplacian_and_flux_error
import Theorems.Thm_NoHair_static_harmonic_lapse_positive_conserved_flux
import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

noncomputable section

open InnerProductSpace
open scoped Laplacian
private abbrev X := ADMPoint
private abbrev I := Fin 3
private noncomputable abbrev e (i : I) : X := EuclideanSpace.single i 1
private noncomputable abbrev pd := spatialADMPartial

private lemma quartic_integrable (q : X → ℝ) (cq : Continuous q) (R C : ℝ) (cp : 0<C)
    (hq : ∀ x : X, R<‖x‖ → |q x|≤C/‖x‖^4) : Integrable q := by
  let w := fun x : X => (1+‖x‖)^4
  have cw : Continuous (fun x => q x*w x) := cq.mul (by dsimp [w]; fun_prop)
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:X) (max R 1)).exists_bound_of_continuousOn cw.continuousOn
  have wt (x:X) : 0<w x := by dsimp [w]; positivity
  have b (x:X) : |q x| * w x ≤ max D (16*C) := by
    by_cases hx : ‖x‖ ≤ max R 1
    · have z := hD x (show x∈closedBall (0:X) (max R 1) by simpa using hx)
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (wt x)] at z
      exact z.trans (le_max_left _ _)
    · obtain ⟨hr,hr1⟩ := max_lt_iff.mp (lt_of_not_ge hx)
      have wp : w x≤16*‖x‖^4 := by
        calc w x ≤ (2*‖x‖)^4 := by dsimp [w]; gcongr; linarith only [hr1]
             _ = _ := by ring
      have np : ‖x‖≠0 := (zero_lt_one.trans hr1).ne'
      apply (mul_le_mul (hq x hr) wp (wt x).le (by positivity)).trans
      exact (show (C/‖x‖^4)*(16*‖x‖^4)=16*C by field_simp).le.trans (le_max_right _ _)
  have inorm : Integrable (fun x : X => (1+‖x‖)^(-(4:ℝ))) :=
    integrable_one_add_norm (by norm_num : (Module.finrank ℝ X : ℝ)<4)
  apply (inorm.const_mul (max D (16*C))).mono' cq.aestronglyMeasurable
  filter_upwards with x
  have hr : (1+‖x‖)^(-(4:ℝ)) = (w x)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  rw [hr,Real.norm_eq_abs,←div_eq_mul_inv]
  exact (le_div_iff₀ (wt x)).mpr (b x)

private lemma trace_eq (u : X → ℝ) (su : ContDiff ℝ ∞ u) (x:X) :
    (Δ u) x = ∑ i : I, pd i (pd i u) x := by
  have df := (su.fderiv_right (m:=∞) (by simp)).differentiable (by simp) x
  have second (i:I) : pd i (pd i u) x = iteratedFDeriv ℝ 2 u x ![e i,e i] := by
    unfold pd spatialADMPartial
    rw [fderiv_clm_apply (u:=fun _ : X => e i) df (differentiableAt_const _), iteratedFDeriv_two_apply]
    simp
  simp_rw [second]
  simpa only [EuclideanSpace.basisFun_apply,e] using congrFun
    (laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun I ℝ)) x

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ u : ADMPoint → ℝ, ContDiff ℝ 2 u ∧
      (∀ᶠ x in cocompact ADMPoint, u x = 1-N x) ∧
      Tendsto u (cocompact ADMPoint) (𝓝 0) ∧ Integrable (fun z => -(Δ u) z) ∧
      (∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) ∧
      0 < ∫ z, -(Δ u) z := by
  classical
  obtain ⟨R,C,rp,cp,err⟩ := static_lapse_euclidean_laplacian_and_flux_error Ω W N h c
  obtain ⟨F,T,fp,tp,flux⟩ := static_harmonic_lapse_positive_conserved_flux Ω W N h c
  obtain ⟨A,hA⟩ := c.compactComplement.isBounded.exists_norm_le
  let K := max (max A R) T
  have kp : 0<K := tp.trans_le (le_max_right _ _)
  let χ : ContDiffBump (0:X) := ⟨K+1,K+2,by linarith,by linarith⟩
  let u := fun x : X => (1-χ x)*(1-N x)
  have cn {x:X} (hx : K<‖x‖) : ContDiffAt ℝ ∞ N x := by
    apply c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (c.extendsAcross (subset_closure ?_)))
    by_contra hn
    exact hx.not_ge ((hA x hn).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have su : ContDiff ℝ ∞ u := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : K<‖x‖
    · exact (contDiffAt_const.sub χ.contDiff.contDiffAt).mul (contDiffAt_const.sub (cn hx))
    · have ins : x ∈ ball (0:X) χ.rIn := by
        rw [mem_ball,dist_zero_right]
        change ‖x‖<K+1
        linarith only [le_of_not_gt hx]
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (0:ℝ)) x).congr_of_eventuallyEq
      filter_upwards [χ.eventuallyEq_one_of_mem_ball ins] with y hy
      change χ y=1 at hy
      simp [u,hy]
  have outer {x:X} (hx : K+2<‖x‖) : u x=1-N x := by
    have z := χ.zero_of_le_dist (x:=x) (by simpa only [dist_zero_right] using hx.le)
    simp [u,z]
  have localEq {x:X} (hx : K+2<‖x‖) :
      u =ᶠ[𝓝 x] (fun y => 1-N y) :=
    (show ∀ᶠ y in 𝓝 x, K+2<‖y‖ from continuous_norm.continuousAt.tendsto (isOpen_Ioi.mem_nhds hx)).mono fun _ hy => outer hy
  have atinf (B:ℝ) : ∀ᶠ x : X in cocompact X, B<‖x‖ := tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop B)
  have lim : Tendsto u (cocompact X) (𝓝 0) := by
    obtain ⟨r0,c0,_,cp0,h0⟩ := c.falloff 0
    apply squeeze_zero_norm' (a:=fun x:X => c0/‖x‖)
    · filter_upwards [atinf (K+2),atinf r0] with x hx hr
      rw [outer hx,Real.norm_eq_abs,abs_sub_comm]
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] using (h0 x hr).1
    · exact tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
  have lap {x:X} (hx : K+2<‖x‖) : (Δ u) x = -(Δ N) x := by
    rw [(laplacian_congr_nhds (localEq hx)).self_of_nhds]
    have z := (contDiffAt_const (c:=(1:ℝ)) : ContDiffAt ℝ 2 (fun _ : X => (1:ℝ)) x).laplacian_sub
      (contDiffAt_infty.mp (cn (x:=x) (by linarith only [hx])) 2)
    change (Δ ((fun _ : X => (1:ℝ)) - N)) x = _
    simpa only [laplacian_const,Pi.zero_apply,zero_sub] using z
  have quart (x:X) (hx : K+2<‖x‖) : |(Δ u) x| ≤ C/‖x‖^4 := by
    rw [lap hx,abs_neg]
    exact (err x (lt_of_le_of_lt ((le_max_right A R).trans (le_max_left _ _)) (by linarith only [hx]))).1
  let q := fun x : X => -(Δ u) x
  have smpd (i:I) : ContDiff ℝ ∞ (pd i u) :=
    (su.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have cq : Continuous q := by
    have eq : q = fun x => -(∑ i : I, pd i (pd i u) x) := funext fun x => congrArg Neg.neg (trace_eq u su x)
    rw [eq]
    exact (continuous_finsetSum _ fun i _ =>
      (((smpd i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).continuous).neg
  have iq : Integrable q := quartic_integrable q cq _ C cp (fun x hx => by simpa [q] using quart x hx)
  refine ⟨u,contDiff_infty.mp su 2,(atinf _).mono fun _ hx => outer hx,lim,iq,
    ⟨K+2,C,by linarith,cp,quart⟩,?_⟩
  let V := fun x : X => WithLp.toLp 2 (fun i : I => -pd i u x)
  have cv : ContDiff ℝ ∞ V := PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun i => (smpd i).neg)
  have dV (x:X) : (∑ i : I, (fderiv ℝ V x (e i)) i) = q x := by
    rw [show q x = -(∑ i:I, pd i (pd i u) x) from congrArg Neg.neg (trace_eq u su x),←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    let proj : X →L[ℝ] ℝ := PiLp.proj 2 (fun _ : I => ℝ) i
    have eq := (proj.hasFDerivAt.comp x (cv.differentiable (by simp) x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => -pd i u y) x = proj.comp (fderiv ℝ V x) at eq
    have z := congrArg (fun L : X →L[ℝ] ℝ => L (e i)) eq
    change (proj.comp (fderiv ℝ V x)) (e i) = -(fderiv ℝ (pd i u) x (e i))
    simpa only [fderiv_fun_neg,ContinuousLinearMap.neg_apply] using z.symm
  let eu := fun (r:ℝ) (n:ADMSphere) => inner ℝ (V (r • (n:X))) (n:X)
  let ph := fun (r:ℝ) (n:ADMSphere) => ∑ i : I, (Real.sqrt (h (r • (n:X))).det *
      staticRaisedGradient N h i (r • (n:X)))*(n:X) i
  let Q := fun r : ℝ => ∫ x in ball (0:X) r, q x
  have balls : (⋃ r : ℝ, ball (0:X) r) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨‖x‖+1,by simp⟩
  have qlim : Tendsto Q atTop (𝓝 (∫ x, q x)) := by
    have t := tendsto_setIntegral_of_monotone (fun r:ℝ => measurableSet_ball (x:=(0:X)) (ε:=r))
      (s:=fun r:ℝ => ball (0:X) r) (fun _ _ hr => ball_subset_ball hr) iq.integrableOn
    simpa only [balls,setIntegral_univ,Q] using t
  have elim : Tendsto (fun r => Q r-F) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun r:ℝ => (3*C*admSurfaceMeasure.real univ)/r)
    · filter_upwards [eventually_gt_atTop (K+2)] with r hr
      have rp' : 0<r := by linarith
      have fl : r^2*(∫ n, ph r n ∂admSurfaceMeasure)=F := flux r (lt_of_le_of_lt (le_max_right _ _) (by linarith only [hr]))
      have st : Q r = r^2*(∫ n, eu r n ∂admSurfaceMeasure) := by
        have z := EuclideanSpace.integral_divergence_ball_three V (cv.of_le (by simp)) r rp'
        simpa only [←dV,Q,eu,e] using z
      have euI : Integrable (eu r) admSurfaceMeasure := by
        have ce : Continuous (eu r) := (cv.continuous.comp ((continuous_const_smul r).comp continuous_subtype_val)).inner continuous_subtype_val
        exact ce.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have phI : Integrable (ph r) admSurfaceMeasure := by
        by_contra hbad
        rw [integral_undef hbad,mul_zero] at fl
        exact fp.ne' fl.symm
      have sums (n:ADMSphere) : ‖eu r n-ph r n‖≤3*(C/r^3) := by
        let x := r • (n:X)
        have unorm : ‖(n:X)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
        have nx : ‖x‖=r := by rw [show ‖x‖=‖r • (n:X)‖ from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos rp',unorm,mul_one]
        have gx : K+2<‖x‖ := nx.symm ▸ hr
        have hcn := (cn (by linarith only [gx])).differentiableAt (by simp)
        have gn (i:I) : -pd i u x = pd i N x := by
          have de : fderiv ℝ u x = fderiv ℝ (fun z => 1-N z) x := (localEq gx).fderiv_eq
          change -(fderiv ℝ u x (e i)) = fderiv ℝ N x (e i)
          rw [de,fderiv_fun_sub (differentiableAt_const _) hcn,fderiv_const_apply]
          simp
        have actual : eu r n - ph r n = ∑ i:I, (pd i N x-Real.sqrt (h x).det*staticRaisedGradient N h i x)*(n:X) i := by
          simp only [eu,ph,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,V,WithLp.ofLp_toLp,sub_mul,Finset.sum_sub_distrib]
          change (∑ i:I, (n:X) i * (-pd i u x)) - _ = _
          simp_rw [gn]
          congr 1
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [actual,Real.norm_eq_abs]
        have eb := (err x (lt_of_le_of_lt ((le_max_right A R).trans (le_max_left _ _)) (by linarith only [gx]))).2
        rw [nx] at eb
        calc _ ≤ ∑ i:I, |(pd i N x - Real.sqrt (h x).det*staticRaisedGradient N h i x)*(n:X) i| := Finset.abs_sum_le_sum_abs _ _
             _ ≤ ∑ _i:I, C/r^3 := Finset.sum_le_sum fun i _ => by
               rw [abs_mul,abs_sub_comm]
               have nb : |(n:X) i| ≤ 1 := by simpa only [Real.norm_eq_abs,unorm] using PiLp.norm_apply_le (n:X) i
               exact (mul_le_of_le_one_right (abs_nonneg _) nb).trans (eb i)
             _ = _ := by simp [Fin.sum_univ_three] <;> ring
      rw [st,←fl,←mul_sub,←integral_sub euI phI,norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      apply (mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const (Eventually.of_forall sums)) (sq_nonneg r)).trans
      exact le_of_eq (by field_simp [rp'.ne'] <;> ring)
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have eq : (∫ x, q x)-F=0 := tendsto_nhds_unique (qlim.sub tendsto_const_nhds) elim
  change 0<∫ x, q x
  linarith only [eq,fp]
