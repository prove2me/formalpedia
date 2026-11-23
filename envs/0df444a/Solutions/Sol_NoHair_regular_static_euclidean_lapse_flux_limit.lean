-- Prove2me | solution 1 for NoHair.regular_static_euclidean_lapse_flux_limit
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:44:31.85881+00:00
-- url     : https://prove2.me/submissions/0e925716-c134-418e-8c2c-1df6b4ea88b5

import Theorems.Thm_NoHair_static_harmonic_lapse_positive_conserved_flux
import Mathlib.Analysis.InnerProductSpace.Laplacian
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

private lemma ct_sum3 {Y : Type*} [TopologicalSpace Y] {y : Y} {f : Fin 3 → Y → ℝ}
    (hf : ∀ i,ContinuousAt (f i) y) : ContinuousAt (fun z => ∑ i,f i z) y := by
  simpa only [Fin.sum_univ_three,Pi.add_def] using ((hf 0).add (hf 1)).add (hf 2)

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ

private lemma matrix_inv_at {A : Mat} (hd : A.det ≠ 0) :
    ContinuousAt (fun B : Mat => B⁻¹) A := by
  apply continuousAt_matrix_inv A
  rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext (fun r => Ring.inverse_eq_inv r)]
  exact continuousAt_inv₀ hd

private lemma matrix_weight_at {A : Mat} (hd : A.det ≠ 0) (i j : I) :
    ContinuousAt (fun B : Mat => Real.sqrt B.det*B⁻¹ i j) A :=
  (Real.continuous_sqrt.continuousAt.comp continuous_id.matrix_det.continuousAt).mul
    (((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp (matrix_inv_at hd))))

private lemma sphere_rad {r : ℝ} (hr : 0 ≤ r) (n : ADMSphere) : ‖r • (n:X)‖=r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,mem_sphere_zero_iff_norm.mp n.property,mul_one]

private lemma sphere_event {P : X → Prop} (hp : ∀ᶠ z in cocompact X,P z) :
    ∀ᶠ r : ℝ in atTop,∀ n : ADMSphere,P (r • (n:X)) := by
  rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop,eventually_comap] at hp
  filter_upwards [hp,eventually_ge_atTop (0:ℝ)] with r hr hr0
  exact fun n => hr _ (sphere_rad hr0 n)

private lemma decompose_covector (L : X →L[ℝ] ℝ) (v : X) :
    L v=∑ i : I,L (EuclideanSpace.single i 1)*v i := by
  have e : (∑ i : I,v i • (EuclideanSpace.single i 1 : X))=v := by
    ext j
    simp [PiLp.smul_apply,PiLp.single_apply,Pi.single_apply,ite_mul,mul_ite]
  calc
    _ = L (∑ i : I,v i • (EuclideanSpace.single i 1 : X)) := congrArg L e.symm
    _ = _ := by simp [mul_comm]

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ m : ℝ, 0 < m ∧ Tendsto (fun r : ℝ => r^2 *
      ∫ n : ADMSphere, fderiv ℝ N (r • (n:ADMPoint)) (n:ADMPoint) ∂admSurfaceMeasure) atTop (𝓝 m) := by
  let Q:=fun i j (x : X) => Real.sqrt (h x).det*(h x)⁻¹ i j
  let p:=fun i (x : X) => spatialADMPartial i N x
  let E:=fun i (x : X) => ∑ j : I,((1:Mat) i j-Q i j x)*(‖x‖^2*p j x)
  let D:=fun (r : ℝ) (n : ADMSphere) => ∑ i : I,E i (r • (n:X))*(n:X) i
  let H:=fun (r : ℝ) (n : ADMSphere) => ∑ i : I,
    (Real.sqrt (h (r • (n:X))).det * staticRaisedGradient N h i (r • (n:X))) * (n:X) i
  let G:=fun (r : ℝ) (n : ADMSphere) => fderiv ℝ N (r • (n:X)) (n:X)
  obtain ⟨B,hB,hout⟩:=c.compactComplement.isBounded.exists_pos_norm_lt
  have hw {x : X} (hx : B<‖x‖) : x∈W := by
    apply c.extendsAcross
    apply subset_closure
    by_contra hn
    exact (not_lt_of_ge hx.le) (hout x hn)
  have ch {x : X} (hx : x∈W) : ContinuousAt h x := continuousAt_pi.mpr fun i =>
    continuousAt_pi.mpr fun j => ((c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds hx)).continuousAt
  obtain ⟨R,C,_,cp,hd⟩:=c.falloff 0
  have hfar : Tendsto h (cocompact X) (𝓝 (1:Mat)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
    · filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R] with x hx
      simpa only [norm_iteratedFDeriv_zero,Nat.zero_add,pow_one] using (hd x hx).2 i j
    · exact (tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop)
  have wlim (i j : I) : Tendsto (Q i j) (cocompact X) (𝓝 ((1:Mat) i j)) := by
    simpa [Q,Function.comp_def] using (matrix_weight_at (A:=(1:Mat)) (by simp) i j).tendsto.comp hfar
  obtain ⟨R₁,C₁,_,hp,h₁⟩:=c.falloff 1
  have bound (j : I) : IsBoundedUnder (·≤·) (cocompact X) (fun x => ‖‖x‖^2*p j x‖) := by
    refine ⟨C₁,?_⟩
    change ∀ᶠ x in cocompact X, ‖‖x‖^2*p j x‖≤C₁
    filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R₁,
      (tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop 0] with x hxr hx0
    have e:=(h₁ x hxr).1
    simp only [norm_iteratedFDeriv_one,fderiv_sub_const] at e
    have b : ‖p j x‖ ≤ ‖fderiv ℝ N x‖ := by
      simpa [p,spatialADMPartial] using (fderiv ℝ N x).le_opNorm (EuclideanSpace.single j 1)
    have v:=(le_div_iff₀ (sq_pos_of_pos hx0)).mp (b.trans e)
    simpa [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖x‖),mul_comm] using v
  have elim (i : I) : Tendsto (E i) (cocompact X) (𝓝 0) := by
    have each (j : I) : Tendsto (fun x => ((1:Mat) i j-Q i j x)*(‖x‖^2*p j x)) (cocompact X) (𝓝 0) := by
      apply Tendsto.zero_mul_isBoundedUnder_le _ (bound j)
      simpa only [sub_self] using (tendsto_const_nhds (x:=(1:Mat) i j)).sub (wlim i j)
    simpa only [E,Fin.sum_univ_three,zero_add] using ((each 0).add (each 1)).add (each 2)
  have small : Tendsto (fun r => ∫ n,D r n ∂admSurfaceMeasure) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let V:=admSurfaceMeasure.real univ
    let η:=ε/(6*(V+1))
    have hv : 0≤V := ENNReal.toReal_nonneg
    have hη : 0<η := by dsimp [η]; positivity
    have es (i : I) : ∀ᶠ z in cocompact X, |E i z|<η := by
      simpa only [Real.dist_eq,sub_zero] using (Metric.tendsto_nhds.mp (elim i) η hη)
    filter_upwards [sphere_event (es 0),sphere_event (es 1),sphere_event (es 2)] with r e0 e1 e2
    have uni (n : ADMSphere) : ‖D r n‖ ≤ 3*η := by
      have all (i : I) : |E i (r • (n:X))|≤η := by fin_cases i <;> first | exact (e0 n).le | exact (e1 n).le | exact (e2 n).le
      have cor (i : I) : |(n:X) i|≤1 := (PiLp.norm_apply_le (n:X) i).trans_eq (mem_sphere_zero_iff_norm.mp n.property)
      change |∑ i : I,E i (r • (n:X))*(n:X) i| ≤ _
      calc
        _ ≤ ∑ i : I, |E i (r • (n:X))*(n:X) i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : I, η := Finset.sum_le_sum (fun i _ => by rw [abs_mul]; simpa only [mul_one] using mul_le_mul (all i) (cor i) (abs_nonneg _) hη.le)
        _ = _ := by simp <;> ring
    have b := norm_setIntegral_le_of_norm_le_const (μ:=admSurfaceMeasure) (s:=univ)
      (measure_lt_top _ _) (fun n _ => uni n)
    rw [Measure.restrict_univ] at b
    change ‖∫ n,D r n ∂admSurfaceMeasure‖ ≤ 3*η*V at b
    rw [dist_zero_right]
    apply b.trans_lt
    have h1 : 0<6*(V+1) := by positivity
    dsimp only [η]
    field_simp [h1]
    nlinarith only [mul_nonneg hε.le hv,hε]
  have identity (r : ℝ) (hr : 0≤r) (n : ADMSphere) : D r n=r^2*(G r n-H r n) := by
    dsimp only [D,E,Q,G,H,p,staticRaisedGradient]
    rw [decompose_covector,sphere_rad hr]
    simp only [Fin.sum_univ_three,Matrix.one_apply,ite_true,ite_false,Fin.isValue,one_mul,zero_mul,spatialADMPartial]
    simp only [if_neg (by decide : (0:I) ≠ 1),if_neg (by decide : (0:I) ≠ 2),
      if_neg (by decide : (1:I) ≠ 0),if_neg (by decide : (1:I) ≠ 2),
      if_neg (by decide : (2:I) ≠ 0),if_neg (by decide : (2:I) ≠ 1),if_pos rfl,ite_true,one_mul,zero_mul]
    ring
  obtain ⟨m,L,hm,hL,flux⟩:=static_harmonic_lapse_positive_conserved_flux Ω W N h c
  refine ⟨m,hm,?_⟩
  have shifted : Tendsto (fun r : ℝ => (∫ n,D r n ∂admSurfaceMeasure)+m) atTop (𝓝 m) := by
    simpa only [zero_add] using small.add (tendsto_const_nhds (x:=m))
  apply shifted.congr'
  filter_upwards [eventually_gt_atTop (max B L)] with r hr
  obtain ⟨rb,rl⟩:=max_lt_iff.mp hr
  have rp := hL.trans rl
  have wc (n : ADMSphere) : r • (n:X)∈W := hw (by simpa only [sphere_rad rp.le n] using rb)
  have sm (n : ADMSphere) := c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (wc n))
  have plane : Continuous (fun n : ADMSphere => r • (n:X)) := by fun_prop
  have dNr (n : ADMSphere) : ContinuousAt (fun a : ADMSphere => fderiv ℝ N (r • (a:X))) n :=
    ((sm n).fderiv_right (m:=∞) (by simp)).continuousAt.comp' (f:=fun a : ADMSphere => r • (a:X)) (x:=n) plane.continuousAt
  have chr (n : ADMSphere) : ContinuousAt (fun a : ADMSphere => h (r • (a:X))) n :=
    (ch (wc n)).comp' (f:=fun a : ADMSphere => r • (a:X)) (x:=n) plane.continuousAt
  have cnG : Continuous (G r) := continuous_iff_continuousAt.mpr fun n =>
    (dNr n).clm_apply continuous_subtype_val.continuousAt
  have cnH : Continuous (H r) := by
    apply continuous_iff_continuousAt.mpr
    intro n
    have hp' := c.positiveMetric _ (wc n)
    have detn := ((h (r • (n:X))).isUnit_iff_isUnit_det.mp hp'.isUnit).ne_zero
    have hinv : ContinuousAt (fun a : ADMSphere => (h (r • (a:X)))⁻¹) n :=
      (matrix_inv_at detn).comp' (f:=fun a : ADMSphere => h (r • (a:X))) (x:=n) (chr n)
    have ic (i j : I) : ContinuousAt (fun a : ADMSphere => (h (r • (a:X)))⁻¹ i j) n :=
      continuousAt_pi.mp (continuousAt_pi.mp hinv i) j
    have dc : ContinuousAt (fun a : ADMSphere => (h (r • (a:X))).det) n :=
      continuous_id.matrix_det.continuousAt.comp' (f:=fun a : ADMSphere => h (r • (a:X))) (x:=n) (chr n)
    apply ct_sum3
    intro i
    apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.mul
    · exact Real.continuous_sqrt.continuousAt.comp' (f:=fun a : ADMSphere => (h (r • (a:X))).det) (x:=n) dc
    · apply ct_sum3
      intro j
      exact (ic i j).mul ((dNr n).clm_apply (continuousAt_const (y:=(EuclideanSpace.single j 1 : X))))
  have ig:=cnG.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
  have ih:=cnH.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
  change (∫ n,D r n ∂admSurfaceMeasure)+m = r^2*∫ n,G r n ∂admSurfaceMeasure
  simp_rw [identity r rp.le]
  rw [integral_const_mul,integral_sub ig ih,←flux r rl]
  change r^2*((∫ n,G r n ∂admSurfaceMeasure)-(∫ n,H r n ∂admSurfaceMeasure))+
    r^2*(∫ n,H r n ∂admSurfaceMeasure)=_
  ring
