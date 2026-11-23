-- Prove2me | solution 1 for NoHair.regular_static_lapse_euclidean_poisson_source
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:41:15.563834+00:00
-- url     : https://prove2.me/submissions/1fd64248-797c-4c96-a6d8-5076007354ae

import Theorems.Thm_NoHair_static_lapse_euclidean_laplacian_decay
import Theorems.Thm_NoHair_regular_static_euclidean_lapse_flux_limit
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

private lemma ct_sum3 {Y : Type*} [TopologicalSpace Y] {y : Y} {f : Fin 3 → Y → ℝ}
    (hf : ∀ i,ContinuousAt (f i) y) : ContinuousAt (fun z => ∑ i,f i z) y := by
  simpa only [Fin.sum_univ_three,Pi.add_def] using ((hf 0).add (hf 1)).add (hf 2)

private abbrev X := ADMPoint

private lemma lap_cont {f : X → ℝ} (cf : ContDiff ℝ ∞ f) : Continuous (Δ f) := by
  simp_rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ),
    iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply continuous_iff_continuousAt.mpr
  intro z
  have cf' := (cf.contDiffAt (x:=z)).fderiv_right (m:=∞) (by simp)
  have cf'' := (cf'.fderiv_right (m:=∞) (by simp)).continuousAt
  exact ct_sum3 (fun _ => (cf''.clm_apply continuousAt_const).clm_apply continuousAt_const)

private lemma lap_int {q : X → ℝ} (cq : Continuous q) {R C : ℝ} (hC : 0<C)
    (hd : ∀ x : X, R<‖x‖ → |q x|≤C/‖x‖^4) : Integrable q := by
  let K:=closedBall (0:X) (max 1 R)
  have hK : IsCompact K := isCompact_closedBall _ _
  rw [←integrableOn_univ,← union_compl_self K,integrableOn_union]
  refine ⟨cq.continuousOn.integrableOn_compact hK,?_⟩
  have hint := integrable_one_add_norm (E:=X) (μ:=volume) (r:=(4:ℝ))
    (by norm_num [finrank_euclideanSpace] : (Module.finrank ℝ X : ℝ)<4)
  apply ((hint.const_mul (16*C)).integrableOn).mono' cq.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=volume) hK.isClosed.measurableSet.compl] with x hx
  have hr : max 1 R < ‖x‖ := by simpa only [K,mem_compl_iff,mem_closedBall_zero_iff,not_le] using hx
  have zero := zero_lt_one.trans (max_lt_iff.mp hr).1
  change |q x|≤16*C*(1+‖x‖)^(-4:ℝ)
  apply (hd x (max_lt_iff.mp hr).2).trans
  rw [Real.rpow_neg (by positivity : 0≤1+‖x‖) (4:ℝ),show (1+‖x‖)^(4:ℝ)=(1+‖x‖)^4 by norm_cast,←div_eq_mul_inv]
  apply (div_le_div_iff₀ (pow_pos zero 4) (by positivity)).2
  have a:=pow_le_pow_left₀ (by positivity : 0≤1+‖x‖) (by linarith [(max_lt_iff.mp hr).1] : 1+‖x‖≤2*‖x‖) 4
  nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr a)]

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ u : ADMPoint → ℝ, ContDiff ℝ 2 u ∧
      (∀ᶠ x in cocompact ADMPoint, u x = 1-N x) ∧
      Tendsto u (cocompact ADMPoint) (𝓝 0) ∧ Integrable (fun z => -(Δ u) z) ∧
      (∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) ∧
      0 < ∫ z, -(Δ u) z := by
  obtain ⟨B,hB,hout⟩:=c.compactComplement.isBounded.exists_pos_norm_lt
  have hw {x : X} (hx : B<‖x‖) : x∈W := by
    apply c.extendsAcross
    apply subset_closure
    by_contra hn
    exact (not_lt_of_ge hx.le) (hout x hn)
  let b : ContDiffBump (0:X) := ⟨B+1,B+2,by linarith,by linarith⟩
  let u := fun x : X => (1-b x)*(1-N x)
  have cu : ContDiff ℝ ∞ u := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : B<‖z‖
    · exact (contDiffAt_const.sub b.contDiff.contDiffAt).mul
        (contDiffAt_const.sub (c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (hw hz))))
    · have hb : z∈ball (0:X) b.rIn := by
        rw [mem_ball_zero_iff]; change ‖z‖<B+1; linarith
      have e : u =ᶠ[𝓝 z] (fun _ => (0:ℝ)) :=
        (b.eventuallyEq_one_of_mem_ball hb).mono (fun y hy => by change b y=1 at hy; simp [u,hy])
      exact contDiffAt_const.congr_of_eventuallyEq e
  have he {x : X} (hx : B+2<‖x‖) : u x=1-N x := by
    have e:b x=0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact hx.le)
    simp [u,e]
  have loc {x : X} (hx : B+2<‖x‖) : u =ᶠ[𝓝 x] (fun y => 1-N y) := by
    have hbig : ∀ᶠ y : X in 𝓝 x, B+2<‖y‖ := (continuous_norm.tendsto x) (isOpen_Ioi.mem_nhds hx)
    exact hbig.mono fun _ hy => he hy
  have ev : ∀ᶠ x : X in cocompact X, u x=1-N x :=
    ((tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop (B+2)).mono fun _ hy => he hy
  obtain ⟨R₀,C₀,_,hC₀,d₀⟩:=c.falloff 0
  have hu0 : Tendsto u (cocompact X) (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun x => C₀/‖x‖)
    · filter_upwards [ev,(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R₀] with x hx hr
      rw [hx,Real.norm_eq_abs,abs_sub_comm]
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] using (d₀ x hr).1
    · exact tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
  obtain ⟨R,C,hR,hC,hd⟩:=static_lapse_euclidean_laplacian_decay Ω W N h c
  let S:=max R (B+2)
  have hS : 0<S := hR.trans_le (le_max_left _ _)
  have tail (x : X) (hx : S<‖x‖) : |(Δ u) x|≤C/‖x‖^4 := by
    obtain ⟨hr,hb⟩:=max_lt_iff.mp hx
    have hn := (c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (hw (by linarith : B<‖x‖)))).of_le
      (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)
    have leq:=(InnerProductSpace.laplacian_congr_nhds (loc hb)).self_of_nhds
    change (Δ u) x=(Δ ((fun _ : X => (1:ℝ))-N)) x at leq
    rw [leq,(contDiffAt_const : ContDiffAt ℝ 2 (fun _ : X => (1:ℝ)) x).laplacian_sub hn]
    simpa using hd x hr
  let q:=fun z => -(Δ u) z
  have qi : Integrable q := lap_int (lap_cont cu).neg hC (fun x hx => by simpa [q] using tail x hx)
  have tv : Tendsto (fun r : ℝ => ∫ z in ball (0:X) r,q z) atTop (𝓝 (∫ z,q z)) := by
    have e:=tendsto_setIntegral_of_monotone (μ:=volume) (f:=q) (s:=fun r : ℝ => ball (0:X) r)
      (fun _ => measurableSet_ball) (fun _ _ h => ball_subset_ball h) qi.integrableOn
    have full : (⋃ r : ℝ,ball (0:X) r)=univ := by
      ext x; simp only [mem_iUnion,mem_ball,dist_zero_right,mem_univ,iff_true]; exact ⟨‖x‖+1,by linarith⟩
    simpa only [full,Measure.restrict_univ] using e
  obtain ⟨m,hm,hf⟩:=regular_static_euclidean_lapse_flux_limit Ω W N h c
  have Vp : 0<volume.real (ball (0:X) 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ zero_lt_one).ne' (measure_ball_lt_top ..).ne
  have tt : Tendsto (fun r : ℝ => ∫ z in ball (0:X) r,q z) atTop (𝓝 m) := by
    apply hf.congr'
    filter_upwards [eventually_gt_atTop (B+2)] with r hr
    have rp : 0<r := by linarith
    have extD (n : ADMSphere) : fderiv ℝ u (0+r • (n:X)) (n:X) = -fderiv ℝ N (r • (n:X)) (n:X) := by
      have nr : ‖r • (n:X)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos rp,mem_sphere_zero_iff_norm.mp n.property,mul_one]
      have eq := (loc (x:=r • (n:X)) (nr.symm ▸ hr)).fderiv_eq (𝕜:=ℝ)
      rw [zero_add,eq,fderiv_const_sub]; rfl
    have eq:=HunterPDE.Harmonic.sphereAverage_radial_eq_ball_laplacian (n:=3) (by decide) (x:=(0:X)) rp
      (fun y _ => (cu.of_le (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt (x:=y))
    rw [average_eq,setAverage_eq] at eq
    simp_rw [extD] at eq
    rw [integral_neg,Measure.toSphere_real_apply_univ] at eq
    simp only [smul_eq_mul,finrank_euclideanSpace,Fintype.card_fin] at eq
    have vr : volume.real (ball (0:X) r) = r^3*volume.real (ball (0:X) 1) := by
      rw [measureReal_def,volume.addHaar_ball_of_pos _ rp,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
      simp [measureReal_def,finrank_euclideanSpace]
    rw [vr] at eq
    change r^2*(∫ n : ADMSphere,fderiv ℝ N (r • (n:X)) (n:X) ∂admSurfaceMeasure) = ∫ z in ball (0:X) r,-(Δ u) z
    rw [integral_neg]
    push_cast at eq
    field_simp [Vp.ne',rp.ne'] at eq
    linarith only [eq]
  have positive : 0<∫ z,q z := by rw [tendsto_nhds_unique tv tt]; exact hm
  exact ⟨u,cu.of_le (WithTop.coe_le_coe.mpr le_top),ev,hu0,qi,⟨S,C,hS,hC,tail⟩,positive⟩
