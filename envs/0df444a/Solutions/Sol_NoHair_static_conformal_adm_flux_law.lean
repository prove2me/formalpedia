-- Prove2me | solution 1 for NoHair.static_conformal_adm_flux_law
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:51:47.883006+00:00
-- url     : https://prove2.me/submissions/4c7a211d-a4d2-46f2-8944-606330bac877

import Definitions.Def_NoHair_staticSliceADM

open NoHair Filter Set
open scoped Topology ContDiff Manifold
open Metric MeasureTheory

private abbrev X := ADMPoint
private abbrev S := ADMSphere
private abbrev H3 := ADMPoint → Matrix (Fin 3) (Fin 3) ℝ

private lemma conformal_partial {N : X → ℝ} {h : H3} {x : X} {i j : Fin 3}
    (cn : DifferentiableAt ℝ N x) (ch : DifferentiableAt ℝ (fun y => h y i j) x) (k : Fin 3) :
    spatialADMPartial k (fun y => staticPositiveMetric N h y i j) x =
      ((1+N x)/2)^4 * spatialADMPartial k (fun y => h y i j) x +
      2 * ((1+N x)/2)^3 * h x i j * spatialADMPartial k N x := by
  let f := fun t : ℝ => ((1+t)/2)^4
  have der : HasDerivAt f (2*((1+N x)/2)^3) (N x) := by
    have a : HasDerivAt (fun t : ℝ => (1+t)/2) (1/2) (N x) :=
      ((hasDerivAt_id (N x)).const_add 1).div_const 2
    have b := a.pow 4
    convert b using 1 <;> first | rfl | (norm_num [f,id_eq] <;> ring)
  have he := ((der.comp_hasFDerivAt x cn.hasFDerivAt).mul ch.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => staticPositiveMetric N h y i j) x = _ at he
  unfold spatialADMPartial
  rw [he]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,Function.comp_apply,f]
  ring

private lemma algebra_bounds {w t : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 2) (ht : 0 ≤ t)
    (hw1 : |w-1| ≤ t) :
    |w^4-1| ≤ 15*t ∧ ∀ a d : ℝ, |a-d| ≤ t → |d| ≤ 1 → |w^3*a-d| ≤ 15*t := by
  have w2 : w^2 ≤ 4 := by exact (pow_le_pow_left₀ hw hw' 2).trans_eq (by norm_num)
  have w3 : w^3 ≤ 8 := by exact (pow_le_pow_left₀ hw hw' 3).trans_eq (by norm_num)
  have w2n : 0 ≤ w^2 := sq_nonneg _
  have w3n : 0 ≤ w^3 := pow_nonneg hw _
  have term4 : |w^4-1| ≤ 15*t := calc
    |w^4-1| = |w-1| * (w^3+w^2+w+1) := by
      rw [show w^4-1=(w-1)*(w^3+w^2+w+1) by ring,abs_mul,abs_of_nonneg (by positivity : 0 ≤ w^3+w^2+w+1)]
    _ ≤ t*15 := mul_le_mul hw1 (by linarith) (by positivity) ht
    _ = _ := by ring
  have term3 : |w^3-1| ≤ 7*t := calc
    |w^3-1| = |w-1| * (w^2+w+1) := by
      rw [show w^3-1=(w-1)*(w^2+w+1) by ring,abs_mul,abs_of_nonneg (by positivity : 0 ≤ w^2+w+1)]
    _ ≤ t*7 := mul_le_mul hw1 (by linarith) (by positivity) ht
    _ = _ := by ring
  refine ⟨term4,?_⟩
  intro a d ha hd
  calc |w^3*a-d| = |w^3*(a-d)+(w^3-1)*d| := by congr 1;ring
       _ ≤ |w^3| * |a-d|+|w^3-1| * |d| := by rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
       _ ≤ 8*t+(7*t)*1 := add_le_add (mul_le_mul (by simpa only [abs_of_nonneg w3n] using w3) ha (abs_nonneg _) (by norm_num))
         (mul_le_mul term3 hd (abs_nonneg _) (by positivity))
       _ = _ := by ring

private lemma sphere_norm (n:S) : ‖(n:X)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using n.property

private lemma point_bound (N : X → ℝ) (h : H3) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) (hCr : C ≤ r)
    (n : S) (cn : ContDiffAt ℝ 1 N (r • (n:X)))
    (ch : ∀ i j, ContDiffAt ℝ 1 (fun z => h z i j) (r • (n:X)))
    (vn : |N (r • (n:X))-1| ≤ C / r)
    (vh : ∀ i j, |h (r • (n:X)) i j - (1:Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C / r)
    (dn0 : ∀ i, |r^2 * spatialADMPartial i N (r • (n:X))| ≤ C)
    (dh0 : ∀ i j k, |r^2 * spatialADMPartial k (fun y => h y i j) (r • (n:X))| ≤ C) :
    |staticADMDensity (staticPositiveMetric N h) r n - staticADMDensity h r n +
      4*staticLapseDensity N r n| ≤ 810*C ^ 2 / r := by
  let x := r • (n:X)
  let w := (1+N x)/2
  let t := C / r
  let d := (1 : Matrix (Fin 3) (Fin 3) ℝ)
  let dh := fun k i j => r^2 * spatialADMPartial k (fun y => h y i j) x
  let dn := fun i => r^2 * spatialADMPartial i N x
  have ht : 0 ≤ t := div_nonneg hC.le hr.le
  have ht1 : t ≤ 1 := (div_le_one hr).mpr hCr
  change |N x-1| ≤ t at vn
  have wab : |w-1| ≤ t := by
    change |(1+N x)/2-1| ≤ t
    rw [show (1+N x)/2-1=(N x-1)/2 by ring, abs_div]
    norm_num
    linarith
  have nw := abs_le.mp vn
  have wpos : 0 ≤ w := by dsimp only [w];linarith [nw.1]
  have wle : w ≤ 2 := by dsimp only [w];linarith [nw.2]
  obtain ⟨cw,hmat⟩ := algebra_bounds wpos wle ht wab
  have md (i j : Fin 3) : |w^3*h x i j-d i j| ≤ 15*t := hmat _ _ (vh i j) (by
    classical
    by_cases eq : i=j <;> simp [d,Matrix.one_apply,eq])
  have ea (i j : Fin 3) : |dh j i j - dh i j j| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith only [dh0 i j j,dh0 j j i])
  let E := fun (i j : Fin 3) =>
    ((w^4-1)*(dh j i j-dh i j j) + 2*((w^3*h x i j-d i j)*dn j) -
      2*((w^3*h x j j-d j j)*dn i)) * (n:X) i
  have eab (i j : Fin 3) : |E i j| ≤ 90*t*C := by
    have a := mul_le_mul cw (ea i j) (abs_nonneg _) (by positivity : 0 ≤ 15*t)
    have b := mul_le_mul (md i j) (dn0 j) (abs_nonneg _) (by positivity : 0 ≤ 15*t)
    have c := mul_le_mul (md j j) (dn0 i) (abs_nonneg _) (by positivity : 0 ≤ 15*t)
    have vn' : |(n:X) i| ≤ 1 := by
      simpa only [Real.norm_eq_abs,sphere_norm] using (PiLp.norm_apply_le (n:X) i)
    dsimp only [E]
    rw [abs_mul]
    calc _ ≤ (90*t*C)*1 := mul_le_mul (by
           refine (abs_sub _ _).trans ?_
           have tri := abs_add_le ((w^4-1)*(dh j i j-dh i j j)) (2*((w^3*h x i j-d i j)*dn j))
           simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at tri ⊢
           change |w^3*h x i j-d i j| * |dn j| ≤ 15*t*C at b
           change |w^3*h x j j-d j j| * |dn i| ≤ 15*t*C at c
           linarith only [tri,a,b,c]) vn' (abs_nonneg _) (by positivity)
         _ = _ := mul_one _
  have jet (k i j : Fin 3) : r^2 * spatialADMPartial k (fun y => staticPositiveMetric N h y i j) x =
      w^4 * dh k i j + 2*w^3*h x i j*dn k := by
    rw [conformal_partial (cn.differentiableAt one_ne_zero) ((ch i j).differentiableAt one_ne_zero)]
    dsimp only [w,dh,dn];ring
  have identical : staticADMDensity (staticPositiveMetric N h) r n - staticADMDensity h r n +
      4*staticLapseDensity N r n = ∑ i, ∑ j, E i j := by
    let dh' := fun (k i j : Fin 3) => r^2 * spatialADMPartial k (fun y => staticPositiveMetric N h y i j) x
    change (∑ i : Fin 3, ∑ j : Fin 3, (dh' j i j - dh' i j j) * (n:X) i) -
      (∑ i : Fin 3, ∑ j : Fin 3, (dh j i j - dh i j j) * (n:X) i) +
      4 * (∑ i : Fin 3, dn i * (n:X) i) = _
    have jeteq : dh' = fun k i j => w^4 * dh k i j + 2*w^3*h x i j*dn k :=
      funext fun k => funext fun i => funext fun j => jet k i j
    rw [jeteq]
    simp +decide [Fin.sum_univ_three,E,d,Matrix.one_apply]
    <;> ring
  rw [identical]
  calc |∑ i, ∑ j, E i j| ≤ ∑ i, |∑ j, E i j| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 90*t*C := Finset.sum_le_sum (fun i _ =>
         (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => eab i j)))
       _ = _ := by simp [Fin.sum_univ_three,t];ring

private lemma partial_on_sphere (f : X → ℝ) (r : ℝ) (k : Fin 3)
    (hf : ∀ n : S, ContDiffAt ℝ 1 f (r • (n:X))) :
    Continuous (fun n : S => spatialADMPartial k f (r • (n:X))) := by
  apply continuous_iff_continuousAt.mpr
  intro n
  have p : ContinuousAt (fun x => spatialADMPartial k f x) (r • (n:X)) :=
    ((hf n).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  exact ContinuousAt.comp (f := fun v : S => r • (v:X)) p
    (show ContinuousAt (fun v : S => r • (v:X)) n from (continuous_const_smul r).continuousAt.comp continuous_subtype_val.continuousAt)

private lemma integrable_adm (h : H3) (r : ℝ)
    (hf : ∀ (n : S) i j, ContDiffAt ℝ 1 (fun y => h y i j) (r • (n:X))) :
    Integrable (staticADMDensity h r) admSurfaceMeasure := by
  have c : Continuous (staticADMDensity h r) := by
    unfold staticADMDensity
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_const.mul (partial_on_sphere _ r j (fun n => hf n i j))).sub
      (continuous_const.mul (partial_on_sphere _ r i (fun n => hf n j j)))).mul
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  exact c.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem solution (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hdec : HasStaticFirstOrderFalloff N h) :
    Tendsto (fun r : ℝ => staticADMFlux (staticPositiveMetric N h) r - staticADMFlux h r
      + staticLapseFlux N r) atTop (𝓝 0) := by
  obtain ⟨R,C,hR,hC,dec⟩ := hdec
  let err := fun (r : ℝ) (n:S) => staticADMDensity (staticPositiveMetric N h) r n -
    staticADMDensity h r n + 4*staticLapseDensity N r n
  have size (r : ℝ) (hr : 0 < r) (n : S) : ‖r • (n:X)‖ = r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]
  have small : Tendsto (fun r => ∫ n : S, err r n ∂admSurfaceMeasure) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun r : ℝ => (810*C ^ 2*admSurfaceMeasure.real univ) / r)
    · filter_upwards [eventually_gt_atTop (max R C)] with r hr
      have rp := hR.trans (max_lt_iff.mp hr).1
      have hbound (n : S) : ‖err r n‖ ≤ 810*C ^ 2 / r := by
        have hh := dec (r • (n:X)) (by rw [size r rp n]; exact (max_lt_iff.mp hr).1)
        rw [size r rp n] at hh
        exact point_bound N h rp hC (max_lt_iff.mp hr).2.le n hh.1 hh.2.1 hh.2.2.1
          hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2
      apply (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)).trans
      apply le_of_eq
      ring
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have eq : (fun r => staticADMFlux (staticPositiveMetric N h) r - staticADMFlux h r + staticLapseFlux N r)
      =ᶠ[atTop] (fun r => (∫ n : S, err r n ∂admSurfaceMeasure)/(16*Real.pi)) := by
    filter_upwards [eventually_gt_atTop R] with r hr
    have atn (n:S) := dec (r • (n:X)) (by rw [size r (hR.trans hr) n]; exact hr)
    have Ncont (n:S) := (atn n).1
    have Hcont (n:S) := (atn n).2.1
    have orig := integrable_adm h r Hcont
    have newMetric := integrable_adm (staticPositiveMetric N h) r (fun n i j =>
      ((((contDiffAt_const.add (Ncont n)).div_const 2).pow 4).mul (Hcont n i j)))
    have lc : Continuous (staticLapseDensity N r) := by
      unfold staticLapseDensity
      refine continuous_finsetSum _ fun i _ => ?_
      exact (continuous_const.mul (partial_on_sphere _ r i Ncont)).mul
        ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
    have li := lc.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
    have si : Integrable (fun n : S => staticADMDensity (staticPositiveMetric N h) r n -
        staticADMDensity h r n) admSurfaceMeasure := newMetric.sub orig
    have mi : Integrable (fun n : S => 4*staticLapseDensity N r n) admSurfaceMeasure := li.const_mul 4
    dsimp only [staticADMFlux,staticLapseFlux,err]
    rw [integral_add si mi,integral_sub newMetric orig,integral_const_mul]
    ring
  exact (by simpa using small.div_const (16*Real.pi) :
    Tendsto (fun r => (∫ n:S, err r n ∂admSurfaceMeasure)/(16*Real.pi)) atTop (𝓝 0)).congr' eq.symm

