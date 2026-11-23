-- Prove2me | solution 1 for NoHair.spherical_mean_lapse_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:28:00.158849+00:00
-- url     : https://prove2.me/submissions/f70b3763-a4d7-42f2-ac04-843b8736f004

import Theorems.Thm_NoHair_translated_ball_source_uniform_bound
import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_continuousOn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

private abbrev X := ADMPoint
local instance : (cocompact X).IsCountablyGenerated := by
  rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop]
  infer_instance
local instance : NeZero admSurfaceMeasure := ⟨(volume : Measure X).toSphere_ne_zero⟩

private lemma mass_measurable {q : X → ℝ} (hi : Integrable q) (x : X) :
    Measurable (fun t : ℝ => (∫ z in ball x (t*‖x‖),q z)/t^2) := by
  have mono (f : X → ℝ) (hf : Integrable f) (hn : ∀ z, 0≤f z) :
      Monotone (fun t : ℝ => ∫ z in ball x (t*‖x‖), f z) := by
    intro a b hab
    apply setIntegral_mono_set hf.integrableOn (ae_of_all _ hn)
    exact ae_of_all _ (fun z hz => ball_subset_ball (mul_le_mul_of_nonneg_right hab (norm_nonneg x)) hz)
  let a:=fun z => |q z|
  let b:=fun z => |q z|-q z
  have ha : Integrable a := hi.abs
  have hb : Integrable b := hi.abs.sub hi
  have he (t : ℝ) : (∫ z in ball x (t*‖x‖),a z)-(∫ z in ball x (t*‖x‖),b z)=
      ∫ z in ball x (t*‖x‖),q z := by
    rw [←integral_sub ha.integrableOn hb.integrableOn]
    simp [a,b]
  apply Measurable.div _ (measurable_id.pow_const 2)
  have hm := (mono a ha (fun z => abs_nonneg _)).measurable.sub
    (mono b hb (fun z => sub_nonneg.mpr (le_abs_self _))).measurable
  change Measurable (fun t : ℝ => (∫ z in ball x (t*‖x‖),a z)-(∫ z in ball x (t*‖x‖),b z)) at hm
  simpa only [he] using hm

private lemma majorant_int (K : ℝ) : IntegrableOn (fun t : ℝ => K/(t+1)^2) (Ioi 0) := by
  have e:=integrableOn_add_rpow_Ioi_of_lt (a:=(-2:ℝ)) (c:=0) (m:=1) (by norm_num) (by norm_num)
  apply (e.const_mul K).congr
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))] with t ht
  change K*(t+1)^(-2:ℝ)=K/(t+1)^2
  simp only [Real.rpow_neg (by linarith [mem_Ioi.mp ht] : 0≤t+1) (2:ℝ),Real.rpow_two,div_eq_mul_inv]

private lemma ball_real' (x : X) {r : ℝ} (hr : 0<r) :
    volume.real (ball x r)=r^3*volume.real (ball (0:X) 1) := by
  rw [measureReal_def,volume.addHaar_ball_of_pos x hr,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
  simp [measureReal_def,finrank_euclideanSpace]

open HunterPDE.Harmonic

private lemma avg_far {u : X → ℝ} (cu : Continuous u) (h0 : Tendsto u (cocompact X) (𝓝 0))
    (x : X) {r : ℝ} (hr : 0<r) : Tendsto (fun t : ℝ => sphereAverage u x (t*r)) atTop (𝓝 0) := by
  classical
  have int (t : ℝ) : Integrable (fun n : ADMSphere => u (x+(t*r) • n.val)) admSurfaceMeasure := by
    have c : Continuous (fun n : ADMSphere => u (x+(t*r) • n.val)) := by fun_prop
    exact c.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have low (t : ℝ) := exists_le_average (μ:=admSurfaceMeasure) (NeZero.ne _) (int t)
  have high (t : ℝ) := exists_average_le (μ:=admSurfaceMeasure) (NeZero.ne _) (int t)
  choose a ha using low
  choose b hb using high
  have go (w : ℝ → ADMSphere) : Tendsto (fun t : ℝ => u (x+(t*r) • (w t).val)) atTop (𝓝 0) := by
    apply h0.comp
    rw [← Metric.cobounded_eq_cocompact,← tendsto_norm_atTop_iff_cobounded]
    apply Filter.tendsto_atTop.2
    intro L
    filter_upwards [eventually_ge_atTop ((|L|+‖x‖+1)/r)] with t ht
    have he:= (div_le_iff₀ hr).mp ht
    have ht' : 0<t*r := by linarith only [he,abs_nonneg L,norm_nonneg x]
    have en : ‖(w t).val‖=1 := mem_sphere_zero_iff_norm.mp (w t).property
    have ht'': t*r ≤ ‖x+(t*r) • (w t).val‖+‖x‖ := by
      calc
        _ = ‖(t*r) • (w t).val‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht',en,mul_one]
        _ = ‖(x+(t*r) • (w t).val)-x‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    linarith [le_abs_self L]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (go a) (go b) ha hb

theorem solution (u : ADMPoint → ℝ) (hu : ContDiff ℝ 2 u)
    (h0 : Tendsto u (cocompact ADMPoint) (𝓝 0))
    (hi : Integrable (fun z => -(Δ u) z))
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) :
    ∀ᶠ x : ADMPoint in cocompact ADMPoint, (3*volume.real (ball (0:ADMPoint) 1))*‖x‖*u x =
      (∫ t : ℝ in Ioi 0, (∫ z in ball x (t*‖x‖), -(Δ u) z)/t^2) := by
  let q:=fun z => -(Δ u) z
  let V:=volume.real (ball (0:X) 1)
  let A:=3*V
  have hpV : 0<V :=
    ENNReal.toReal_pos (measure_ball_pos _ _ zero_lt_one).ne' (measure_ball_lt_top ..).ne
  have hq : ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ z : X, R<‖z‖ → |q z| ≤ C/‖z‖^4 := by
    simpa [q] using hd
  obtain ⟨K,R,hK,hR,hb⟩ := translated_ball_source_uniform_bound q hi hq
  filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R] with x hx
  let r:=‖x‖
  have hr : 0<r := hR.trans hx
  let F := fun t : ℝ => (∫ z in ball x (t*r),q z)/t^2
  have fint : IntegrableOn F (Ioi 0) := by
    apply (majorant_int K).mono' (mass_measurable hi x).aestronglyMeasurable
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hb x hx t ht)
  let U := fun t : ℝ => -(A*r)*sphereAverage u x (t*r)
  have der (t : ℝ) (ht : t∈Ioi (0:ℝ)) : HasDerivAt U (F t) t := by
    have ht0:=mem_Ioi.mp ht
    have hs := mul_pos ht0 hr
    have e := hasDerivAt_sphereAverage_radial (n:=3) (by decide) (x:=x) hs
      (fun y _ => (hu.of_le (by norm_num : (1:ℕ∞ω)≤2)).contDiffAt (x:=y))
    rw [sphereAverage_radial_eq_ball_laplacian (by decide) hs (fun y _ => hu.contDiffAt (x:=y))] at e
    have e' := ((e.comp t ((hasDerivAt_id t).mul_const r)).const_mul (-(A*r)))
    change HasDerivAt U _ t at e'
    convert e' using 1
    dsimp only [F,q,A,V]
    rw [setAverage_eq,smul_eq_mul,ball_real' x hs,integral_neg]
    push_cast
    have hvn : volume.real (ball (0:X) 1) ≠ 0 := hpV.ne'
    field_simp [ht0.ne',hr.ne',hvn]
    <;> ring
  have ac : ContinuousWithinAt (sphereAverage u x) (Ici (0:ℝ)) 0 := by
    have e := (sphereAverage_continuousOn (x:=x) (r:=1) (by norm_num) hu.continuous.continuousOn)
      0 (show (0:ℝ)∈Icc 0 1 from ⟨le_rfl,zero_le_one⟩)
    simpa only [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsGE zero_lt_one] using e
  have lin : ContinuousWithinAt (fun t : ℝ => t*r) (Ici 0) 0 := (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
  have tc : ContinuousWithinAt U (Ici 0) 0 := by
    have ac' : ContinuousWithinAt (sphereAverage u x) (Ici 0) (0*r) := by simpa using ac
    exact continuousWithinAt_const.mul (ac'.comp (f:=fun t : ℝ => t*r) lin (fun t ht => mul_nonneg ht hr.le))
  have lim : Tendsto U atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:= -(A*r))).mul (avg_far hu.continuous h0 x hr)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto tc der fint lim
  have avg0 : sphereAverage u x 0=u x := by simp [sphereAverage,average_const]
  change A*r*u x=∫ t in Ioi (0:ℝ),F t
  rw [he]
  simp only [U,zero_mul,avg0,neg_mul,zero_sub,neg_neg]
