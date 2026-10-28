-- Prove2me | solution 1 for OAI.CompactMomentVariational.exists_C11_truncated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:16:17.862959+00:00
-- url     : https://prove2.me/submissions/cce84b54-af82-4440-90d4-6860c983f973

import Mathlib
import Definitions.Def_OAIW2LB000

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

namespace CompactMomentVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma values_nonempty {K : Set E} (hK : K.Nonempty) (u : E → ℝ) (z : E) :
    ((fun x => ⟪x,z⟫_ℝ-u x) '' K).Nonempty := hK.image _

lemma values_bdd {K : Set E} {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) (z : E) :
    BddAbove ((fun x => ⟪x,z⟫_ℝ-u x) '' K) := by
  refine ⟨R*‖z‖-m, ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  have hi := real_inner_le_norm x z
  have hn := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg z)
  have hm := hu x hx
  linarith

lemma le_conjugate {K : Set E} {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) {x : E} (hx : x ∈ K) (z : E) :
    ⟪x,z⟫_ℝ-u x ≤ conjugate K u z :=
  le_csSup (values_bdd hR hu z) (mem_image_of_mem _ hx)

lemma conjugate_le {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {z : E} {b : ℝ}
    (h : ∀ x ∈ K, ⟪x,z⟫_ℝ-u x ≤ b) : conjugate K u z ≤ b := by
  apply csSup_le (values_nonempty hK u z)
  rintro _ ⟨x,hx,rfl⟩
  exact h x hx

lemma conjugate_upper {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) (z : E) :
    conjugate K u z ≤ R*‖z‖-m := by
  apply conjugate_le hK
  intro x hx
  have hi := real_inner_le_norm x z
  have hn := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg z)
  have hm := hu x hx
  linarith

lemma conjugate_nonneg {K : Set E} {u : E → ℝ} {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, 0 ≤ u x) (h0 : (0:E) ∈ K)
    (hu0 : u 0=0) (z : E) : 0 ≤ conjugate K u z := by
  simpa [hu0] using le_conjugate hR hu h0 z

lemma conjugate_zero {K : Set E} {u : E → ℝ} {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, 0 ≤ u x) (h0 : (0:E) ∈ K)
    (hu0 : u 0=0) : conjugate K u 0=0 := by
  apply le_antisymm _ (conjugate_nonneg hR hu h0 hu0 0)
  simpa using conjugate_upper ⟨0,h0⟩ hR hu 0

lemma convexOn_conjugate {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) :
    ConvexOn ℝ univ (conjugate K u) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ a b ha hb hab
  apply conjugate_le hK
  intro x hx
  have hz := le_conjugate hR hu hx z
  have hw := le_conjugate hR hu hx w
  dsimp only [smul_eq_mul]
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have habu : (a+b)*u x=u x := by rw [hab,one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hz ha, mul_le_mul_of_nonneg_left hw hb]

lemma conjugate_sub_le {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) (z w : E) :
    conjugate K u z-conjugate K u w ≤ R*‖z-w‖ := by
  apply sub_le_iff_le_add.mpr
  apply conjugate_le hK
  intro x hx
  have hw := le_conjugate hR hu hx w
  have hi := real_inner_le_norm x (z-w)
  rw [inner_sub_right] at hi
  have hn := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg (z-w))
  linarith

lemma conjugate_lipschitz {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {R : ℝ≥0} {m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) :
    LipschitzWith R (conjugate K u) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z w
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := conjugate_sub_le hK hR hu w z
    rw [norm_sub_rev] at h
    linarith
  · exact conjugate_sub_le hK hR hu z w

lemma conjugate_even {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hKe : ∀ x ∈ K, -x ∈ K) (hue : Function.Even u) :
    Function.Even (conjugate K u) := by
  have hle (z : E) : conjugate K u (-z) ≤ conjugate K u z := by
    apply conjugate_le hK
    intro x hx
    simpa only [inner_neg_left,inner_neg_right,hue x] using
      le_conjugate hR hu (hKe x hx) z
  intro z
  apply le_antisymm (hle z)
  simpa using hle (-z)

lemma conjugate_coercive {K : Set E} {u : E → ℝ} {R m r B : ℝ} (hr : 0 ≤ r)
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hrK : Metric.closedBall (0:E) r ⊆ K)
    (hB : ∀ x ∈ Metric.closedBall (0:E) r, u x ≤ B) (z : E) :
    r*‖z‖-B ≤ conjugate K u z := by
  by_cases hz : z=0
  · subst z
    have h0 : (0:E) ∈ Metric.closedBall 0 r := by simpa using hr
    have h := le_conjugate hR hu (hrK h0) (0:E)
    have hb := hB 0 h0
    simp only [inner_zero_right,norm_zero,mul_zero] at *
    linarith
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let x : E := (r/‖z‖) • z
    have hx : x ∈ Metric.closedBall (0:E) r := by
      simp [x,Metric.mem_closedBall,dist_zero_right,norm_smul,abs_of_nonneg hr,hn]
    have hi : ⟪x,z⟫_ℝ=r*‖z‖ := by
      simp only [x,real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    have hl := le_conjugate hR hu (hrK hx) z
    rw [hi] at hl
    linarith [hB x hx]

lemma convex_small_ball_bound {u : E → ℝ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hu : ConvexOn ℝ (Metric.closedBall (0:E) r) u) (hu0 : u 0=0)
    (hB : ∀ x ∈ Metric.closedBall (0:E) r, u x ≤ M) :
    ∀ x ∈ Metric.closedBall (0:E) (r/(M+1)), u x ≤ 1 := by
  intro x hx
  have hMp : 0 < M+1 := by linarith
  let y : E := (M+1) • x
  have hy : y ∈ Metric.closedBall (0:E) r := by
    rw [Metric.mem_closedBall,dist_zero_right] at hx ⊢
    rw [show y=(M+1) • x from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hMp]
    simpa only [mul_comm] using (le_div_iff₀ hMp).mp hx
  have h0 : (0:E) ∈ Metric.closedBall (0:E) r := by simpa using hr.le
  have ha : 0 ≤ (M+1)⁻¹ := inv_nonneg.mpr hMp.le
  have hb : 0 ≤ 1-(M+1)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith))
  have h := hu.2 hy h0 ha hb (by ring)
  have harg : (M+1)⁻¹ • y+(1-(M+1)⁻¹) • (0:E)=x := by
    simp [y,smul_smul,hMp.ne']
  rw [harg,hu0,smul_eq_mul,smul_eq_mul,mul_zero,add_zero] at h
  have hm : (M+1)⁻¹*M ≤ 1 := by
    rw [inv_mul_le_iff₀ hMp]
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_left (hB y hy) ha).trans hm)

section MeanBound
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma convex_ball_mean_bound_at {u : E → ℝ} {r R : ℝ} (_hr : 0 < r)
    (hc : ConvexOn ℝ (Metric.closedBall (0:E) R) u)
    (hn : ∀ y ∈ Metric.closedBall (0:E) R, 0 ≤ u y)
    (hi : IntegrableOn u (Metric.closedBall (0:E) R) μ)
    {x : E} (hx : ‖x‖+r ≤ R) :
    μ.real (Metric.closedBall (0:E) r)*u x ≤ ∫ y in Metric.closedBall (0:E) R, u y ∂μ := by
  let K := Metric.closedBall (0:E) R
  let S := Metric.closedBall (0:E) r
  let f := K.indicator u
  have hi' : Integrable f μ := hi.integrable_indicator measurableSet_closedBall
  have hf : ∀ y, 0 ≤ f y := fun y => Set.indicator_nonneg (fun z hz => hn z hz) y
  have hia : Integrable (fun y => f (x+y)) μ := hi'.comp_add_left x
  have his : Integrable (fun y => f (x-y)) μ := hi'.comp_sub_left x
  have hmS : μ S < ⊤ := (isCompact_closedBall (0:E) r).measure_lt_top
  let : Fact (μ S < ⊤) := ⟨hmS⟩
  have hmid : ∀ y ∈ S, 2*u x ≤ f (x+y)+f (x-y) := by
    intro y hy
    have hyn : ‖y‖ ≤ r := by simpa [S,Metric.mem_closedBall,dist_zero_right] using hy
    have hplus : x+y ∈ K := by
      rw [show K=Metric.closedBall (0:E) R from rfl,Metric.mem_closedBall,dist_zero_right]
      exact (norm_add_le x y).trans (by linarith)
    have hminus : x-y ∈ K := by
      rw [show K=Metric.closedBall (0:E) R from rfl,Metric.mem_closedBall,dist_zero_right]
      exact (norm_sub_le x y).trans (by linarith)
    have h := hc.2 hplus hminus (show (0:ℝ)≤1/2 by norm_num)
      (show (0:ℝ)≤1/2 by norm_num) (show (1:ℝ)/2+1/2=1 by norm_num)
    have havg : (1/2:ℝ) • (x+y)+(1/2:ℝ) • (x-y)=x := by module
    rw [havg] at h
    rw [show f (x+y)=u (x+y) from Set.indicator_of_mem hplus u,
      show f (x-y)=u (x-y) from Set.indicator_of_mem hminus u]
    dsimp only [smul_eq_mul] at h
    linarith
  have hh := setIntegral_mono_on (integrable_const (2*u x)) (hia.add his).integrableOn
    measurableSet_closedBall hmid
  simp only [Pi.add_apply] at hh
  rw [integral_add hia.integrableOn his.integrableOn,integral_const] at hh
  have hla : (∫ y in S, f (x+y) ∂μ) ≤ ∫ y, f y ∂μ := by
    calc
      _ ≤ ∫ y, f (x+y) ∂μ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun y => hf (x+y))) hia
      _ = _ := integral_add_left_eq_self f x
  have hls : (∫ y in S, f (x-y) ∂μ) ≤ ∫ y, f y ∂μ := by
    calc
      _ ≤ ∫ y, f (x-y) ∂μ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun y => hf (x-y))) his
      _ = _ := integral_sub_left_eq_self f μ x
  have hfint : (∫ y, f y ∂μ) = ∫ y in Metric.closedBall (0:E) R, u y ∂μ :=
    integral_indicator measurableSet_closedBall
  simp only [Measure.restrict_apply_univ,Measure.real,smul_eq_mul] at hh
  rw [hfint] at hla hls
  change (μ S).toReal*u x ≤ _
  linarith

lemma convex_ball_mean_bound {u : E → ℝ} {r R : ℝ} (_hr : 0 < r) (hrR : 2*r ≤ R)
    (hc : ConvexOn ℝ (Metric.closedBall (0:E) R) u)
    (hn : ∀ y ∈ Metric.closedBall (0:E) R, 0 ≤ u y)
    (hi : IntegrableOn u (Metric.closedBall (0:E) R) μ)
    {x : E} (hx : x ∈ Metric.closedBall (0:E) r) :
    μ.real (Metric.closedBall (0:E) r)*u x ≤ ∫ y in Metric.closedBall (0:E) R, u y ∂μ := by
  let K := Metric.closedBall (0:E) R
  let S := Metric.closedBall (0:E) r
  let f := K.indicator u
  have hi' : Integrable f μ := hi.integrable_indicator measurableSet_closedBall
  have hf : ∀ y, 0 ≤ f y := fun y => Set.indicator_nonneg (fun z hz => hn z hz) y
  have hia : Integrable (fun y => f (x+y)) μ := hi'.comp_add_left x
  have his : Integrable (fun y => f (x-y)) μ := hi'.comp_sub_left x
  have hmS : μ S < ⊤ := (isCompact_closedBall (0:E) r).measure_lt_top
  let : Fact (μ S < ⊤) := ⟨hmS⟩
  have hmid : ∀ y ∈ S, 2*u x ≤ f (x+y)+f (x-y) := by
    intro y hy
    have hxn : ‖x‖ ≤ r := by simpa [Metric.mem_closedBall,dist_zero_right] using hx
    have hyn : ‖y‖ ≤ r := by simpa [S,Metric.mem_closedBall,dist_zero_right] using hy
    have hplus : x+y ∈ K := by
      rw [show K=Metric.closedBall (0:E) R from rfl,Metric.mem_closedBall,dist_zero_right]
      exact (norm_add_le x y).trans (by linarith)
    have hminus : x-y ∈ K := by
      rw [show K=Metric.closedBall (0:E) R from rfl,Metric.mem_closedBall,dist_zero_right]
      exact (norm_sub_le x y).trans (by linarith)
    have h := hc.2 hplus hminus (show (0:ℝ)≤1/2 by norm_num)
      (show (0:ℝ)≤1/2 by norm_num) (show (1:ℝ)/2+1/2=1 by norm_num)
    have havg : (1/2:ℝ) • (x+y)+(1/2:ℝ) • (x-y)=x := by module
    rw [havg] at h
    rw [show f (x+y)=u (x+y) from Set.indicator_of_mem hplus u,
      show f (x-y)=u (x-y) from Set.indicator_of_mem hminus u]
    dsimp only [smul_eq_mul] at h
    linarith
  have hh := setIntegral_mono_on (integrable_const (2*u x)) (hia.add his).integrableOn
    measurableSet_closedBall hmid
  simp only [Pi.add_apply] at hh
  rw [integral_add hia.integrableOn his.integrableOn,integral_const] at hh
  have hla : (∫ y in S, f (x+y) ∂μ) ≤ ∫ y, f y ∂μ := by
    calc
      _ ≤ ∫ y, f (x+y) ∂μ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun y => hf (x+y))) hia
      _ = _ := integral_add_left_eq_self f x
  have hls : (∫ y in S, f (x-y) ∂μ) ≤ ∫ y, f y ∂μ := by
    calc
      _ ≤ ∫ y, f (x-y) ∂μ := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun y => hf (x-y))) his
      _ = _ := integral_sub_left_eq_self f μ x
  have hfint : (∫ y, f y ∂μ) = ∫ y in Metric.closedBall (0:E) R, u y ∂μ :=
    integral_indicator measurableSet_closedBall
  simp only [Measure.restrict_apply_univ,Measure.real,smul_eq_mul] at hh
  rw [hfint] at hla hls
  change (μ S).toReal*u x ≤ _
  linarith

lemma convex_ball_probability_bound {u : E → ℝ} {r R d : ℝ}
    (hr : 0 < r) (hrR : 2*r ≤ R) (hd : 0 < d)
    (hc : ConvexOn ℝ (Metric.closedBall (0:E) R) u)
    (hn : ∀ y, 0 ≤ u y) (ν : Measure E)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) R) ≤ ν)
    (hi : Integrable u ν) {x : E} (hx : x ∈ Metric.closedBall (0:E) r) :
    d*μ.real (Metric.closedBall (0:E) r)*u x ≤ ∫ y, u y ∂ν := by
  have hid := hi.mono_measure hν
  have hiBall : IntegrableOn u (Metric.closedBall (0:E) R) μ := by
    exact (integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hd)) ENNReal.ofReal_ne_top).mp hid
  have hb := convex_ball_mean_bound μ hr hrR hc (fun y _ => hn y) hiBall hx
  calc
    d*μ.real (Metric.closedBall (0:E) r)*u x ≤ d*(∫ y in Metric.closedBall (0:E) R, u y ∂μ) := by
      nlinarith [mul_le_mul_of_nonneg_left hb hd.le]
    _ = ∫ y, u y ∂(ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) R)) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hd.le,smul_eq_mul]
    _ ≤ ∫ y, u y ∂ν := integral_mono_measure hν (Eventually.of_forall hn) hi

lemma convex_ball_probability_bound_at {u : E → ℝ} {r R d : ℝ}
    (hr : 0 < r) (hd : 0 < d)
    (hc : ConvexOn ℝ (Metric.closedBall (0:E) R) u)
    (hn : ∀ y, 0 ≤ u y) (ν : Measure E)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) R) ≤ ν)
    (hi : Integrable u ν) {x : E} (hx : ‖x‖+r ≤ R) :
    d*μ.real (Metric.closedBall (0:E) r)*u x ≤ ∫ y, u y ∂ν := by
  have hid := hi.mono_measure hν
  have hiBall : IntegrableOn u (Metric.closedBall (0:E) R) μ :=
    (integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hd)) ENNReal.ofReal_ne_top).mp hid
  have hb := convex_ball_mean_bound_at μ hr hc (fun y _ => hn y) hiBall hx
  calc
    d*μ.real (Metric.closedBall (0:E) r)*u x ≤ d*(∫ y in Metric.closedBall (0:E) R, u y ∂μ) := by
      nlinarith [mul_le_mul_of_nonneg_left hb hd.le]
    _ = ∫ y, u y ∂(ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) R)) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hd.le,smul_eq_mul]
    _ ≤ ∫ y, u y ∂ν := integral_mono_measure hν (Eventually.of_forall hn) hi

end MeanBound

section Partition
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integrable_exp_neg_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c*‖x‖)) μ := by
  let r : ℝ := Module.finrank ℝ E + 1
  have hr : (Module.finrank ℝ E : ℝ) < r := by dsimp [r]; linarith
  have hi : Integrable (fun x : E => (1+‖x‖)^(-r)) μ := integrable_one_add_norm hr
  have hl : LocallyIntegrable (fun x : E => Real.exp (-c*‖x‖)) μ :=
    (show Continuous (fun x : E => Real.exp (-c*‖x‖)) by fun_prop).locallyIntegrable
  have ht : Tendsto (fun x : E => (1:ℝ)+‖x‖) (cocompact E) atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop
  have hO := (isLittleO_exp_neg_mul_rpow_atTop hc (-r)).isBigO.comp_tendsto ht
  have hO' := hO.const_mul_left (Real.exp c)
  have hfn : (fun x : E => Real.exp c * Real.exp (-c * (1+‖x‖))) =
      (fun x : E => Real.exp (-c*‖x‖)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Function.comp_apply] at hO'
  rw [hfn] at hO'
  exact hl.integrable_of_isBigO_cocompact hO' (hi.integrableAtFilter (cocompact E))

lemma integral_exp_neg_norm_scale {c : ℝ} (hc : 0 < c) :
    (∫ x : E, Real.exp (-c*‖x‖) ∂μ) =
    (c^Module.finrank ℝ E)⁻¹ * ∫ x : E, Real.exp (-‖x‖) ∂μ := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, neg_mul, smul_eq_mul]
    using Measure.integral_comp_smul_of_nonneg μ (fun x : E => Real.exp (-‖x‖)) c (hR:=hc.le)

lemma tail_integrable {φ : E → ℝ} (hφ : Continuous φ) {c b : ℝ}
    (hc : 0 < c) (hl : ∀ z, c*‖z‖-b ≤ φ z) :
    Integrable (fun z => Real.exp (-φ z)) μ := by
  refine ((integrable_exp_neg_norm μ hc).const_mul (Real.exp b)).mono'
    (Real.continuous_exp.comp hφ.neg).aestronglyMeasurable ?_
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hl z])

lemma partition_bound {φ : E → ℝ} (hφ : Continuous φ) {c b : ℝ}
    (hc : 0 < c) (hl : ∀ z, c*‖z‖-b ≤ φ z) :
    (∫ z, Real.exp (-φ z) ∂μ) ≤
      Real.exp b * (c^Module.finrank ℝ E)⁻¹ * ∫ z : E, Real.exp (-‖z‖) ∂μ := by
  calc
    _ ≤ ∫ z, Real.exp b * Real.exp (-c*‖z‖) ∂μ := by
      apply integral_mono (tail_integrable μ hφ hc hl)
        ((integrable_exp_neg_norm μ hc).const_mul _)
      intro z
      dsimp only
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hl z])
    _ = _ := by rw [integral_const_mul,integral_exp_neg_norm_scale μ hc]; ring

lemma log_partition_bound {φ : E → ℝ} (hφ : Continuous φ) {c b : ℝ}
    (hc : 0 < c) (hl : ∀ z, c*‖z‖-b ≤ φ z) :
    Real.log (∫ z, Real.exp (-φ z) ∂μ) ≤
      b - (Module.finrank ℝ E)*Real.log c +
        Real.log (∫ z : E, Real.exp (-‖z‖) ∂μ) := by
  have hI : 0 < ∫ z, Real.exp (-φ z) ∂μ :=
    integral_exp_pos (tail_integrable μ hφ hc hl)
  have hN : 0 < ∫ z : E, Real.exp (-‖z‖) ∂μ := by
    exact integral_exp_pos (by simpa using integrable_exp_neg_norm μ (show (0:ℝ)<1 by norm_num))
  have h := Real.log_le_log hI (partition_bound μ hφ hc hl)
  rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (inv_ne_zero (pow_ne_zero _ hc.ne')))
    hN.ne', Real.log_mul (Real.exp_ne_zero _) (inv_ne_zero (pow_ne_zero _ hc.ne')),
    Real.log_exp, Real.log_inv, Real.log_pow] at h
  simpa [sub_eq_add_neg] using h

end Partition

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [BorelSpace E] in
lemma ball_real_pos {r : ℝ} (hr : 0 < r) :
    0 < μ.real (Metric.closedBall (0:E) r) := by
  apply ENNReal.toReal_pos
  · apply ne_of_gt
    exact (Metric.isOpen_ball.measure_pos μ ⟨0,by simpa using hr⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  · exact (isCompact_closedBall (0:E) r).measure_ne_top

lemma mean_conjugate_lower {u : E → ℝ} {r R d : ℝ}
    (hr : 0 < r) (hrR : 2*r ≤ R) (hd : 0 < d)
    (hc : ConvexOn ℝ (Metric.closedBall (0:E) R) u)
    (hn : ∀ y, 0 ≤ u y) (hu0 : u 0=0) (ν : Measure E)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) R) ≤ ν)
    (hi : Integrable u ν) (z : E) :
    (r/((∫ y, u y ∂ν)/(d*μ.real (Metric.closedBall (0:E) r))+1))*‖z‖-1 ≤
      conjugate (Metric.closedBall (0:E) R) u z := by
  let C := d*μ.real (Metric.closedBall (0:E) r)
  let M := (∫ y, u y ∂ν)/C
  have hC : 0 < C := mul_pos hd (ball_real_pos μ hr)
  have hM : 0 ≤ M := div_nonneg (integral_nonneg hn) hC.le
  have hMp : 0 < M+1 := by positivity
  have hrR' : r ≤ R := by linarith
  have hB : ∀ x ∈ Metric.closedBall (0:E) r, u x ≤ M := by
    intro x hx
    apply (le_div_iff₀ hC).mpr
    simpa [C,mul_comm] using convex_ball_probability_bound μ hr hrR hd hc hn ν hν hi hx
  have hSmall : ∀ x ∈ Metric.closedBall (0:E) (r/(M+1)), u x ≤ 1 :=
    convex_small_ball_bound hr hM
      (hc.subset (Metric.closedBall_subset_closedBall hrR') (convex_closedBall _ _)) hu0 hB
  have hsr : r/(M+1) ≤ r := (div_le_iff₀ hMp).mpr (by nlinarith)
  apply conjugate_coercive (le_of_lt (div_pos hr hMp))
    (fun x hx => by simpa [Metric.mem_closedBall,dist_zero_right] using hx)
    (fun x _ => hn x) (Metric.closedBall_subset_closedBall (hsr.trans hrR')) hSmall

lemma logarithmic_growth_bound {N C m : ℝ} (hN : 0 ≤ N) (hC : 0 < C) (hm : 0 ≤ m) :
    N*Real.log (m/C+1) ≤ m/2+C/2+N*Real.log (2*(N+1)/C) := by
  have hA : 0 < 2*(N+1) := by positivity
  have hmC : 0 < m+C := by positivity
  have hq : 0 < (m+C)/(2*(N+1)) := div_pos hmC hA
  have hid : m/C+1 = (m+C)/(2*(N+1))*(2*(N+1)/C) := by
    field_simp
  rw [hid,Real.log_mul hq.ne' (div_ne_zero hA.ne' hC.ne'),mul_add]
  have hl := Real.log_le_sub_one_of_pos hq
  have hcoef : N*((m+C)/(2*(N+1))-1) ≤ (m+C)/2 := by
    have he : (2*(N+1))*((m+C)/(2*(N+1)))=m+C := mul_div_cancel₀ _ hA.ne'
    nlinarith [mul_nonneg hN hq.le]
  have hh := (mul_le_mul_of_nonneg_left hl hN).trans hcoef
  linarith


end
end CompactMomentVariational

open Set Filter
open scoped Topology NNReal

noncomputable section
namespace MomentCompactness
variable {E : Type*} [NormedAddCommGroup E]

lemma normalizedLipschitz_pointwise (R : ℝ≥0) :
    ContinuousMap.toFun '' (normalizedLipschitz (E:=E) R) =
      {f : E → ℝ | LipschitzWith R f ∧ f 0=0} := by
  ext f
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact hg
  · intro hf
    exact ⟨⟨f,hf.1.continuous⟩,hf,rfl⟩

lemma normalizedLipschitz_compact (R : ℝ≥0) :
    IsCompact (normalizedLipschitz (E:=E) R) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [normalizedLipschitz_pointwise]
    apply (isCompact_pi_infinite (fun x : E =>
      (isCompact_Icc : IsCompact (Icc (-(R:ℝ)*‖x‖) ((R:ℝ)*‖x‖))))).of_isClosed_subset
    · exact (isClosed_setOfPred_lipschitzWith R).inter
        (isClosed_eq (continuous_apply 0) continuous_const)
    · intro f hf x
      have h := hf.1.dist_le_mul x 0
      rw [hf.2,Real.dist_eq,sub_zero,dist_zero_right] at h
      simpa only [Set.mem_Icc,neg_mul] using abs_le.mp h
  · exact Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (R:ℝ)*r)
      (by simpa using (show Continuous (fun r : ℝ => (R:ℝ)*r) by fun_prop).tendsto 0) _
      (fun x y f => f.property.1.dist_le_mul x y)

variable [NormedSpace ℝ E]

lemma normalizedLipschitz_subsequence [FiniteDimensional ℝ E]
    {R : ℝ≥0} {f : ℕ → E → ℝ} (hl : ∀ k, LipschitzWith R (f k))
    (h0 : ∀ k, f k 0=0) :
    ∃ (g : E → ℝ) (s : ℕ → ℕ), LipschitzWith R g ∧ g 0=0 ∧ StrictMono s ∧
      TendstoLocallyUniformly (fun k => f (s k)) g atTop := by
  let F : ℕ → C(E,ℝ) := fun k => ⟨f k,(hl k).continuous⟩
  have hm : ∀ k, F k ∈ normalizedLipschitz R := fun k => ⟨hl k,h0 k⟩
  obtain ⟨g,hg,s,hs,ht⟩ := (normalizedLipschitz_compact (E:=E) R).tendsto_subseq hm
  refine ⟨g,s,hg.1,hg.2,hs,?_⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht

end MomentCompactness

namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma conjugate_mono {K L : Set E} {u : E → ℝ} {R m : ℝ}
    (hK : K.Nonempty) (hKL : K ⊆ L) (hR : ∀ x ∈ L, ‖x‖ ≤ R)
    (hu : ∀ x ∈ L, m ≤ u x) (z : E) : conjugate K u z ≤ conjugate L u z := by
  apply conjugate_le hK
  intro x hx
  exact le_conjugate hR hu (hKL hx) z

variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma mean_conjugate_lower_ball {u : E → ℝ} {r S R d : ℝ}
    (hr : 0 < r) (hrS : 2*r ≤ S) (hSR : S < R) (hd : 0 < d)
    (ν : Measure E) (hu : Admissible ν R u)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) (z : E) :
    (r/((∫ y, u y ∂ν)/(d*μ.real (Metric.closedBall (0:E) r))+1))*‖z‖-1 ≤
      conjugate (Metric.ball (0:E) R) u z := by
  have hS : 0 ≤ S := by linarith
  have hs : Metric.closedBall (0:E) S ⊆ Metric.ball (0:E) R := by
    intro x hx
    exact lt_of_le_of_lt hx hSR
  exact (mean_conjugate_lower μ hr hrS hd
    (hu.convex.subset hs (convex_closedBall _ _)) hu.nonneg hu.zero ν hν hu.integrable z).trans
      (conjugate_mono ⟨0,by simpa using hS⟩ hs
        (fun x hx => le_of_lt (by simpa [Metric.mem_ball,dist_zero_right] using hx))
        (fun x _ => hu.nonneg x) z)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma admissible_conjugate_lipschitz {ν : Measure E} {R : ℝ≥0} {u : E → ℝ}
    (hR : 0 < R) (hu : Admissible ν R u) : LipschitzWith R (conjugate (Metric.ball (0:E) R) u) := by
  apply conjugate_lipschitz ⟨0,by simpa using hR⟩
    (fun x hx => le_of_lt (by simpa [Metric.mem_ball,dist_zero_right] using hx))
    (fun x _ => hu.nonneg x)

lemma functional_coercive_ball {u : E → ℝ} {r S R d : ℝ}
    (hr : 0 < r) (hrS : 2*r ≤ S) (hSR : S < R) (hd : 0 < d)
    (ν : Measure E) (hu : Admissible ν R u)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) :
    functional μ ν (Metric.ball (0:E) R) u ≤
      coercivityConstant μ r d - (∫ x, u x ∂ν)/2 := by
  let C := d*μ.real (Metric.closedBall (0:E) r)
  let m := ∫ x, u x ∂ν
  have hC : 0 < C := mul_pos hd (ball_real_pos μ hr)
  have hm : 0 ≤ m := integral_nonneg hu.nonneg
  have hMp : 0 < m/C+1 := by positivity
  have hR : 0 < R := by linarith
  have hcont := (admissible_conjugate_lipschitz (R:=⟨R,hR.le⟩) hR hu).continuous
  have hl := mean_conjugate_lower_ball μ hr hrS hSR hd ν hu hν
  have hb := log_partition_bound μ hcont (div_pos hr hMp) hl
  change Real.log (∫ z, Real.exp (-conjugate (Metric.ball (0:E) R) u z) ∂μ) ≤
    1-(Module.finrank ℝ E)*Real.log (r/(m/C+1))+
      Real.log (∫ z : E, Real.exp (-‖z‖) ∂μ) at hb
  rw [Real.log_div hr.ne' hMp.ne',mul_sub] at hb
  have hg := logarithmic_growth_bound (show (0:ℝ) ≤ Module.finrank ℝ E by positivity) hC hm
  dsimp only [functional,coercivityConstant]
  change Real.log (∫ z, Real.exp (-conjugate (Metric.ball (0:E) R) u z) ∂μ)-m ≤
    1-(Module.finrank ℝ E)*Real.log r+
      Real.log (∫ z : E, Real.exp (-‖z‖) ∂μ)+C/2+
      (Module.finrank ℝ E)*Real.log (2*((Module.finrank ℝ E)+1)/C)-m/2
  linarith

lemma admissible_local_bound {ν : Measure E} {R r S d M : ℝ} {u : E → ℝ}
    (hr : 0 < r) (hSR : S < R) (hd : 0 < d) (hu : Admissible ν R u)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν)
    (hM : (∫ y, u y ∂ν) ≤ M) {x : E} (hx : ‖x‖+r ≤ S) :
    u x ≤ M/(d*μ.real (Metric.closedBall (0:E) r)) := by
  have hC : 0 < d*μ.real (Metric.closedBall (0:E) r) := mul_pos hd (ball_real_pos μ hr)
  apply (le_div_iff₀ hC).mpr
  have hs : Metric.closedBall (0:E) S ⊆ Metric.ball (0:E) R := fun _ hx => lt_of_le_of_lt hx hSR
  have hb := convex_ball_probability_bound_at μ hr hd
    (hu.convex.subset hs (convex_closedBall _ _)) hu.nonneg ν hν hu.integrable hx
  have hh : u x*(d*μ.real (Metric.closedBall (0:E) r)) ≤ ∫ y,u y ∂ν := by
    simpa [mul_comm] using hb
  exact hh.trans hM

lemma uniform_conjugate_coercive {ν : Measure E} {R r S d M : ℝ} {u : E → ℝ}
    (hr : 0 < r) (hrS : 2*r ≤ S) (hSR : S < R) (hd : 0 < d) (_hM : 0 ≤ M)
    (hu : Admissible ν R u)
    (hν : ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν)
    (hm : (∫ y, u y ∂ν) ≤ M) (z : E) :
    (r/(M/(d*μ.real (Metric.closedBall (0:E) r))+1))*‖z‖-1 ≤
      conjugate (Metric.ball (0:E) R) u z := by
  have hC : 0 < d*μ.real (Metric.closedBall (0:E) r) := mul_pos hd (ball_real_pos μ hr)
  have hn : 0 ≤ ∫ y, u y ∂ν := integral_nonneg hu.nonneg
  have hmC := div_le_div_of_nonneg_right hm hC.le
  have hq := div_le_div_of_nonneg_left hr.le (by positivity : 0 < (∫ y,u y ∂ν)/
    (d*μ.real (Metric.closedBall (0:E) r))+1) (by linarith : (∫ y,u y ∂ν)/(d*μ.real (Metric.closedBall (0:E) r))+1 ≤
      M/(d*μ.real (Metric.closedBall (0:E) r))+1)
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_right hq (norm_nonneg z)) 1).trans
    (mean_conjugate_lower_ball μ hr hrS hSR hd ν hu hν z)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma convexOn_limit {f : ℕ → E → ℝ} {g : E → ℝ}
    (hc : ∀ n, ConvexOn ℝ univ (f n))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : ConvexOn ℝ univ g := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact le_of_tendsto_of_tendsto (ht (a • x+b • y))
    (((ht x).const_mul a).add ((ht y).const_mul b))
    (Eventually.of_forall fun n => (hc n).2 hx hy ha hb hab)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] in
lemma even_limit {f : ℕ → E → ℝ} {g : E → ℝ}
    (he : ∀ n, Function.Even (f n))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Function.Even g := by
  intro x
  apply tendsto_nhds_unique (ht (-x))
  have hh : (fun n => f n (-x))=(fun n => f n x) := funext fun n => he n x
  rw [hh]
  exact ht x

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma admissible_conjugate_normalized {ν : Measure E} {R : ℝ≥0} {u : E → ℝ}
    (hR : 0 < R) (hu : Admissible ν R u) :
    NormalizedConvex R (conjugate (Metric.ball (0:E) R) u) := by
  have h0 : (0:E) ∈ Metric.ball (0:E) (R:ℝ) := by simpa using hR
  have hKR : ∀ x ∈ Metric.ball (0:E) (R:ℝ), ‖x‖ ≤ R :=
    fun x hx => (by simpa [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < R).le
  exact ⟨admissible_conjugate_lipschitz hR hu,
    conjugate_zero hKR (fun x _ => hu.nonneg x) h0 hu.zero,
    conjugate_nonneg hKR (fun x _ => hu.nonneg x) h0 hu.zero,
    conjugate_even ⟨0,h0⟩ hKR (fun x _ => hu.nonneg x)
      (fun x hx => by simpa [Metric.mem_ball,dist_zero_right] using hx) hu.even,
    convexOn_conjugate ⟨0,h0⟩ hKR (fun x _ => hu.nonneg x)⟩

omit [BorelSpace E] in
lemma admissible_conjugate_subsequence {ν : Measure E} {R : ℝ≥0} {u : ℕ → E → ℝ}
    (hR : 0 < R) (hu : ∀ n, Admissible ν R (u n)) :
    ∃ (φ : E → ℝ) (s : ℕ → ℕ), NormalizedConvex R φ ∧ StrictMono s ∧
      TendstoLocallyUniformly (fun n => conjugate (Metric.ball (0:E) R) (u (s n))) φ atTop := by
  have hp (n : ℕ) := admissible_conjugate_normalized hR (hu n)
  obtain ⟨φ,s,hl,h0,hs,ht⟩ := MomentCompactness.normalizedLipschitz_subsequence
    (fun n => (hp n).lipschitz) (fun n => (hp n).zero)
  have hpt (x : E) : Tendsto (fun n => conjugate (Metric.ball (0:E) R) (u (s n)) x)
      atTop (𝓝 (φ x)) := ht.tendsto_comp hl.continuous.continuousAt tendsto_const_nhds
  refine ⟨φ,s,⟨hl,h0,?_,even_limit (fun n => (hp (s n)).even) hpt,
    convexOn_limit (fun n => (hp (s n)).convex) hpt⟩,hs,ht⟩
  intro x
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hpt x)
    (Eventually.of_forall fun n => (hp (s n)).nonneg x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma conjugate_limit_bdd {K : Set E} {R : ℝ} {u : ℕ → E → ℝ} {φ : E → ℝ}
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ n, ∀ x ∈ K, 0 ≤ u n x)
    (hp : ∀ z, Tendsto (fun n => conjugate K (u n) z) atTop (𝓝 (φ z)))
    (hlocal : ∀ x ∈ K, ∃ B, ∀ n, u n x ≤ B) :
    ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ) := by
  intro x hx
  obtain ⟨B,hB⟩ := hlocal x hx
  refine ⟨B,?_⟩
  rintro _ ⟨z,_,rfl⟩
  apply le_of_tendsto (tendsto_const_nhds.sub (hp z))
  apply Eventually.of_forall
  intro n
  have h := le_conjugate hKR (hu n) hx z
  rw [real_inner_comm z x] at h
  linarith [hB n]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_conjugate_of_bdd {K D : Set E} (hK : K.Nonempty) (hD : Convex ℝ D)
    {u : E → ℝ} (hb : ∀ z ∈ D, BddAbove ((fun x => ⟪x,z⟫_ℝ-u x) '' K)) :
    ConvexOn ℝ D (conjugate K u) := by
  refine ⟨hD, ?_⟩
  intro z hz w hw a b ha hb' hab
  apply conjugate_le hK
  intro x hx
  have hz' := le_csSup (hb z hz) (mem_image_of_mem (fun x => ⟪x,z⟫_ℝ-u x) hx)
  have hw' := le_csSup (hb w hw) (mem_image_of_mem (fun x => ⟪x,w⟫_ℝ-u x) hx)
  change ⟪x,z⟫_ℝ-u x ≤ conjugate K u z at hz'
  change ⟪x,w⟫_ℝ-u x ≤ conjugate K u w at hw'
  simp only [smul_eq_mul]
  rw [inner_add_right,inner_smul_right,inner_smul_right]
  have habu : (a+b)*u x=u x := by rw [hab,one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hz' ha,mul_le_mul_of_nonneg_left hw' hb']

lemma conjugate_even_univ {φ : E → ℝ} (he : Function.Even φ) :
    Function.Even (conjugate univ φ) := by
  intro x
  unfold conjugate
  congr 1
  ext t
  constructor <;> rintro ⟨z,_,rfl⟩
  · exact ⟨-z,mem_univ _,by simp [he z]⟩
  · exact ⟨-z,mem_univ _,by simp [he z]⟩

lemma dualOn_eq {K : Set E} {φ : E → ℝ} {x : E} (hx : x ∈ K) :
    dualOn K φ x=conjugate univ φ x := indicator_of_mem hx _

lemma convexOn_dualOn {K : Set E} (hK : Convex ℝ K) {φ : E → ℝ}
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) :
    ConvexOn ℝ K (dualOn K φ) :=
  (convexOn_conjugate_of_bdd (univ_nonempty) hK hb).congr (fun _ hx => (dualOn_eq hx).symm)

lemma dualOn_nonneg {K : Set E} {φ : E → ℝ} (h0 : φ 0=0)
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) :
    ∀ x, 0 ≤ dualOn K φ x := by
  intro x
  by_cases hx : x ∈ K
  · rw [dualOn_eq hx]
    simpa [conjugate,h0] using le_csSup (hb x hx) (mem_image_of_mem (fun z => ⟪z,x⟫_ℝ-φ z) (mem_univ 0))
  · simp [dualOn,indicator_of_notMem hx]

lemma dualOn_zero {K : Set E} {φ : E → ℝ} (h0 : φ 0=0) (hn : ∀ x, 0 ≤ φ x)
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) :
    dualOn K φ 0=0 := by
  by_cases hx : (0:E) ∈ K
  · apply le_antisymm _ (dualOn_nonneg h0 hb 0)
    rw [dualOn_eq hx]
    apply conjugate_le univ_nonempty
    intro z _
    simpa using hn z
  · simp [dualOn,indicator_of_notMem hx]

lemma dualOn_even_ball {R : ℝ} {φ : E → ℝ} (he : Function.Even φ) :
    Function.Even (dualOn (Metric.ball (0:E) R) φ) := by
  intro x
  by_cases hx : x ∈ Metric.ball (0:E) R
  · have hn : -x ∈ Metric.ball (0:E) R := by simpa [Metric.mem_ball,dist_zero_right] using hx
    rw [dualOn_eq hx,dualOn_eq hn,conjugate_even_univ he]
  · have hn : -x ∉ Metric.ball (0:E) R := by simpa [Metric.mem_ball,dist_zero_right] using hx
    simp [dualOn,indicator_of_notMem hx,indicator_of_notMem hn]

lemma fenchel_dualOn {K : Set E} {φ : E → ℝ}
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) {x : E} (hx : x ∈ K) (z : E) :
    ⟪x,z⟫_ℝ-dualOn K φ x ≤ φ z := by
  rw [dualOn_eq hx]
  have h := le_csSup (hb x hx) (mem_image_of_mem (fun z => ⟪z,x⟫_ℝ-φ z) (mem_univ z))
  change ⟪z,x⟫_ℝ-φ z ≤ conjugate univ φ x at h
  rw [real_inner_comm x z] at h
  linarith

lemma minorant_slope_norm {φ : E → ℝ} {R : ℝ≥0} (hl : LipschitzWith R φ)
    (h0 : φ 0=0) {p : E} {c : ℝ} (hm : ∀ z, ⟪p,z⟫_ℝ+c ≤ φ z) : ‖p‖ ≤ R := by
  have hc : c ≤ 0 := by simpa [h0] using hm 0
  by_contra! hp
  have hn : 0 < ‖p‖ := lt_of_le_of_lt R.coe_nonneg hp
  let A := ‖p‖^2-(R:ℝ)*‖p‖
  have hA : 0 < A := by dsimp [A]; nlinarith
  let t : ℝ := (1-c)/A
  have ht : 0 < t := div_pos (by linarith) hA
  have hdist := hl.dist_le_mul (t • p) 0
  rw [h0,Real.dist_eq,sub_zero,dist_zero_right,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht] at hdist
  have hu : φ (t • p) ≤ (R:ℝ)*(t*‖p‖) := (le_abs_self _).trans hdist
  have hm' := hm (t • p)
  rw [inner_smul_right,real_inner_self_eq_norm_sq] at hm'
  have he : t*A=1-c := div_mul_cancel₀ _ hA.ne'
  dsimp only [A] at he
  nlinarith

variable [FiniteDimensional ℝ E]

theorem conjugate_dualOn_ball {φ : E → ℝ} {R : ℝ≥0} (hR : 0 < R)
    (hl : LipschitzWith R φ) (h0 : φ 0=0) (hn : ∀ x, 0 ≤ φ x)
    (hc : ConvexOn ℝ univ φ)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) :
    conjugate (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ)=φ := by
  have hK : (Metric.ball (0:E) (R:ℝ)).Nonempty := ⟨0,by simpa using hR⟩
  have hKR : ∀ x ∈ Metric.ball (0:E) (R:ℝ), ‖x‖ ≤ R :=
    fun x hx => (by simpa [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < R).le
  have hu := dualOn_nonneg h0 hb
  funext z
  apply le_antisymm (conjugate_le hK (fun x hx => fenchel_dualOn hb hx z))
  suffices hh : ∀ a < φ z, a ≤ conjugate (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ) z by
    by_contra! hh'
    have hh'' := hh ((φ z+conjugate (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ) z)/2) (by linarith)
    linarith
  intro a ha
  obtain ⟨l,c,hm,he⟩ := hc.exists_affine_le_of_lt (𝕜:=ℝ) (mem_univ z) ha isClosed_univ
    (hl.continuous.lowerSemicontinuous.lowerSemicontinuousOn univ)
  let p : E := (InnerProductSpace.toDual ℝ E).symm l
  have hp (y : E) : ⟪p,y⟫_ℝ=l y := InnerProductSpace.toDual_symm_apply
  have hm' (y : E) : ⟪p,y⟫_ℝ+c ≤ φ y := by
    simpa [Function.comp_def,hp] using hm ⟨y,mem_univ y⟩
  have he' : ⟪p,z⟫_ℝ+c=a := by simpa [hp] using he
  have hpn := minorant_slope_norm hl h0 hm'
  have hbnd {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
      t*a ≤ conjugate (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ) z := by
    have htp : t • p ∈ Metric.ball (0:E) (R:ℝ) := by
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
      exact (mul_le_mul_of_nonneg_left hpn ht).trans_lt (by nlinarith [R.coe_nonneg])
    have hdu : dualOn (Metric.ball (0:E) R) φ (t • p) ≤ -t*c := by
      rw [dualOn_eq htp]
      apply conjugate_le univ_nonempty
      intro y _
      rw [inner_smul_right,real_inner_comm p y]
      have hv := mul_le_mul_of_nonneg_left (hm' y) ht
      have hw := mul_le_mul_of_nonneg_right ht1.le (hn y)
      nlinarith
    have hle := le_conjugate hKR (fun x _ => hu x) htp z
    rw [real_inner_smul_left] at hle
    nlinarith
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)/(n+1))*a) atTop (𝓝 a) := by
    simpa using (tendsto_natCast_div_add_atTop (1:ℝ)).mul_const a
  exact le_of_tendsto ht (Eventually.of_forall fun n =>
    hbnd (div_nonneg (Nat.cast_nonneg n) (by positivity))
      ((div_lt_one (by positivity)).mpr (by linarith)))

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma dualOn_le_liminf {K : Set E} {R : ℝ} {u : ℕ → E → ℝ} {φ : E → ℝ}
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ n, ∀ x ∈ K, 0 ≤ u n x)
    (hp : ∀ z, Tendsto (fun n => conjugate K (u n) z) atTop (𝓝 (φ z))) (x : E) :
    ENNReal.ofReal (dualOn K φ x) ≤ liminf (fun n => ENNReal.ofReal (u n x)) atTop := by
  by_cases hx : x ∈ K
  · by_cases htop : liminf (fun n => ENNReal.ofReal (u n x)) atTop=⊤
    · simp [htop]
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
    rw [dualOn_eq hx]
    apply conjugate_le univ_nonempty
    intro z _
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
    have ht : Tendsto (fun n => ENNReal.ofReal (⟪z,x⟫_ℝ-conjugate K (u n) z)) atTop
        (𝓝 (ENNReal.ofReal (⟪z,x⟫_ℝ-φ z))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub (hp z))
    rw [← ht.liminf_eq]
    apply liminf_le_liminf (Eventually.of_forall fun n => ?_)
    apply ENNReal.ofReal_le_ofReal
    have h := le_conjugate hKR (hu n) hx z
    rw [real_inner_comm z x] at h
    linarith
  · simp [dualOn,indicator_of_notMem hx]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma dualOn_mean_lower_semicontinuous {ν : Measure E} {K : Set E} (hK : IsOpen K)
    (hc : Convex ℝ K) {R : ℝ} {u : ℕ → E → ℝ} {φ : E → ℝ} {m : ℝ}
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ n x, 0 ≤ u n x)
    (hi : ∀ n, Integrable (u n) ν) (h0 : φ 0=0)
    (hp : ∀ z, Tendsto (fun n => conjugate K (u n) z) atTop (𝓝 (φ z)))
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ))
    (hm : Tendsto (fun n => ∫ x, u n x ∂ν) atTop (𝓝 m)) :
    Integrable (dualOn K φ) ν ∧ (∫ x, dualOn K φ x ∂ν) ≤ m := by
  have ham : AEStronglyMeasurable (dualOn K φ) ν :=
    (aestronglyMeasurable_indicator_iff hK.measurableSet).mpr
      ((ConvexOn.continuousOn hK (convexOn_conjugate_of_bdd univ_nonempty hc hb)).aestronglyMeasurable
        hK.measurableSet)
  have hnu := dualOn_nonneg h0 hb
  have hfat : (∫⁻ x, ENNReal.ofReal (dualOn K φ x) ∂ν) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂ν) atTop :=
    (lintegral_mono (dualOn_le_liminf hKR (fun n x _ => hu n x) hp)).trans
      (lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hi n).aestronglyMeasurable.aemeasurable))
  have hei : (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂ν)=
      (fun n => ENNReal.ofReal (∫ x, u n x ∂ν)) :=
    funext fun n => (ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (hu n))).symm
  have hmt : Tendsto (fun n => ENNReal.ofReal (∫ x, u n x ∂ν)) atTop
      (𝓝 (ENNReal.ofReal m)) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hm
  rw [hei,hmt.liminf_eq] at hfat
  have hui : Integrable (dualOn K φ) ν := ⟨ham,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnu)).mpr (hfat.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hui,?_⟩
  have hm0 : 0 ≤ m := le_of_tendsto_of_tendsto tendsto_const_nhds hm
    (Eventually.of_forall fun n => integral_nonneg (hu n))
  rw [← ofReal_integral_eq_lintegral_ofReal hui (Eventually.of_forall hnu)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hm0).mp hfat

variable (μ : Measure E) [μ.IsAddHaarMeasure]
lemma partition_tendsto {f : ℕ → E → ℝ} {φ : E → ℝ} {c b : ℝ} (hc : 0 < c)
    (hf : ∀ n, Continuous (f n)) (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (φ z)))
    (hl : ∀ n z, c*‖z‖-b ≤ f n z) :
    Tendsto (fun n => ∫ z, Real.exp (-f n z) ∂μ) atTop (𝓝 (∫ z, Real.exp (-φ z) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => Real.exp b*Real.exp (-c*‖z‖))
    (fun n => (Real.continuous_exp.comp (hf n).neg).aestronglyMeasurable)
    ((integrable_exp_neg_norm μ hc).const_mul (Real.exp b))
  · intro n
    apply Eventually.of_forall
    intro z
    change |Real.exp (-f n z)| ≤ Real.exp b * Real.exp (-c * ‖z‖)
    rw [abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hl n z])
  · exact Eventually.of_forall fun z =>
      (Real.continuous_exp.tendsto _).comp (ht z).neg

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma admissible_zero (ν : Measure E) (R : ℝ) :
    Admissible ν R (fun _ => 0) :=
  ⟨convexOn_const 0 (convex_ball _ _), fun _ => le_rfl, rfl, fun _ => rfl,
    fun _ _ => rfl, integrable_zero E ℝ ν⟩

lemma admissible_local_bounds {ν : Measure E} {R d M : ℝ} {u : ℕ → E → ℝ}
    (hd : 0 < d) (hu : ∀ n, Admissible ν R (u n))
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν)
    (hM : ∀ n, (∫ y, u n y ∂ν) ≤ M) :
    ∀ x ∈ Metric.ball (0:E) R, ∃ B, ∀ n, u n x ≤ B := by
  intro x hx
  have hxn : ‖x‖ < R := by simpa [Metric.mem_ball,dist_zero_right] using hx
  let r := (R-‖x‖)/4
  let S := (R+‖x‖)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hSR : S < R := by dsimp [S]; linarith
  have hS : 0 ≤ S := by dsimp [S]; linarith [norm_nonneg x]
  refine ⟨M/(d*μ.real (Metric.closedBall (0:E) r)),fun n => ?_⟩
  exact admissible_local_bound μ hr hSR hd (hu n) (hν S hS hSR) (hM n)
    (by dsimp [r,S]; linarith)

lemma limit_dual_admissible {ν : Measure E} {R : ℝ≥0} {d M m : ℝ}
    {u : ℕ → E → ℝ} {φ : E → ℝ} (hR : 0 < R) (hd : 0 < d)
    (hu : ∀ n, Admissible ν R (u n))
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν)
    (hM : ∀ n, (∫ y, u n y ∂ν) ≤ M) (hφ : NormalizedConvex R φ)
    (hp : ∀ z, Tendsto (fun n => conjugate (Metric.ball (0:E) R) (u n) z) atTop (𝓝 (φ z)))
    (hm : Tendsto (fun n => ∫ x, u n x ∂ν) atTop (𝓝 m)) :
    Admissible ν R (dualOn (Metric.ball (0:E) R) φ) ∧
    (∫ x, dualOn (Metric.ball (0:E) R) φ x ∂ν) ≤ m ∧
    conjugate (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ)=φ := by
  have hKR : ∀ x ∈ Metric.ball (0:E) (R:ℝ), ‖x‖ ≤ R :=
    fun x hx => (by simpa [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < R).le
  have hb := conjugate_limit_bdd hKR (fun n x _ => (hu n).nonneg x) hp
    (admissible_local_bounds μ hd hu hν hM)
  obtain ⟨hi,him⟩ := dualOn_mean_lower_semicontinuous Metric.isOpen_ball (convex_ball _ _)
    hKR (fun n => (hu n).nonneg) (fun n => (hu n).integrable) hφ.zero hp hb hm
  refine ⟨⟨convexOn_dualOn (convex_ball _ _) hb, dualOn_nonneg hφ.zero hb,
    dualOn_zero hφ.zero hφ.nonneg hb,dualOn_even_ball hφ.even,?_,hi⟩,him,?_⟩
  · intro x hx
    exact indicator_of_notMem hx _
  · exact conjugate_dualOn_ball hR hφ.lipschitz hφ.zero hφ.nonneg hφ.convex hb

lemma functional_limit_upper {ν : Measure E} {R : ℝ≥0} {d M m a : ℝ}
    {u : ℕ → E → ℝ} {φ : E → ℝ} (hR : 0 < R) (hd : 0 < d) (hM0 : 0 ≤ M)
    (hu : ∀ n, Admissible ν R (u n))
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν)
    (hM : ∀ n, (∫ y, u n y ∂ν) ≤ M) (hφ : NormalizedConvex R φ)
    (hp : ∀ z, Tendsto (fun n => conjugate (Metric.ball (0:E) R) (u n) z) atTop (𝓝 (φ z)))
    (hm : Tendsto (fun n => ∫ x, u n x ∂ν) atTop (𝓝 m))
    (ha : Tendsto (fun n => functional μ ν (Metric.ball (0:E) R) (u n)) atTop (𝓝 a)) :
    Admissible ν R (dualOn (Metric.ball (0:E) R) φ) ∧
    a ≤ functional μ ν (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ) := by
  obtain ⟨had,him,heq⟩ := limit_dual_admissible μ hR hd hu hν hM hφ hp hm
  let r : ℝ := R/4
  let S : ℝ := R/2
  have hRR : (0:ℝ) < R := hR
  have hr : 0 < r := by dsimp [r]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSR : S < R := by dsimp [S]; linarith
  have hrS : 2*r ≤ S := by dsimp [r,S]; linarith
  let c := r/(M/(d*μ.real (Metric.closedBall (0:E) r))+1)
  have hc : 0 < c := div_pos hr (add_pos_of_nonneg_of_pos
    (div_nonneg hM0 (mul_pos hd (ball_real_pos μ hr)).le) zero_lt_one)
  have hl (n : ℕ) (z : E) : c*‖z‖-1 ≤ conjugate (Metric.ball (0:E) R) (u n) z :=
    uniform_conjugate_coercive μ hr hrS hSR hd hM0 (hu n) (hν S hS hSR) (hM n) z
  have hlφ (z : E) : c*‖z‖-1 ≤ φ z :=
    ge_of_tendsto (hp z) (Eventually.of_forall fun n => hl n z)
  have hI : 0 < ∫ z, Real.exp (-φ z) ∂μ :=
    integral_exp_pos (tail_integrable μ hφ.lipschitz.continuous hc hlφ)
  have ht := partition_tendsto μ hc
    (fun n => (admissible_conjugate_lipschitz hR (hu n)).continuous) hp hl
  have htlog : Tendsto (fun n => Real.log (∫ z, Real.exp (-conjugate
      (Metric.ball (0:E) R) (u n) z) ∂μ)) atTop (𝓝 (Real.log (∫ z,Real.exp (-φ z) ∂μ))) :=
    (Real.continuousAt_log hI.ne').tendsto.comp ht
  have heqa : a=Real.log (∫ z,Real.exp (-φ z) ∂μ)-m := tendsto_nhds_unique ha (htlog.sub hm)
  refine ⟨had,?_⟩
  rw [heqa,functional,heq]
  exact sub_le_sub_left him _


lemma maximizing_sequence {ν : Measure E} {R : ℝ≥0} {d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) :
    ∃ (u : ℕ → E → ℝ) (M : ℝ), 0 ≤ M ∧ (∀ n, Admissible ν R (u n)) ∧
      (∀ n, (∫ y, u n y ∂ν) ≤ M) ∧
      Tendsto (fun n => functional μ ν (Metric.ball (0:E) R) (u n)) atTop
        (𝓝 (sSup (valueSet μ ν R))) ∧
      ∀ v, Admissible ν R v → functional μ ν (Metric.ball (0:E) R) v ≤ sSup (valueSet μ ν R) := by
  let r : ℝ := R/4
  let S : ℝ := R/2
  have hRR : (0:ℝ) < R := hR
  have hr : 0 < r := by dsimp [r]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSR : S < R := by dsimp [S]; linarith
  have hrS : 2*r ≤ S := by dsimp [r,S]; linarith
  let C := coercivityConstant μ r d
  have hco (v : E → ℝ) (hv : Admissible ν R v) :
      functional μ ν (Metric.ball (0:E) R) v ≤ C-(∫ x,v x ∂ν)/2 :=
    functional_coercive_ball μ hr hrS hSR hd ν hv (hν S hS hSR)
  have hn : (valueSet μ ν R).Nonempty :=
    ⟨_,fun _ => 0,admissible_zero ν R,rfl⟩
  have hb : BddAbove (valueSet μ ν R) := by
    refine ⟨C,?_⟩
    rintro a ⟨v,hv,rfl⟩
    exact (hco v hv).trans (sub_le_self _ (div_nonneg (integral_nonneg hv.nonneg) (by norm_num)))
  obtain ⟨w,hw,hwt,hwin⟩ := exists_seq_tendsto_sSup hn hb
  choose u hu heq using hwin
  have hbnd (n : ℕ) : (∫ x,u n x ∂ν) ≤ 2*(C-w 0) := by
    have h1 := hco (u n) (hu n)
    rw [heq n] at h1
    have h2 := hw (Nat.zero_le n)
    linarith
  refine ⟨u,2*(C-w 0),(integral_nonneg (hu 0).nonneg).trans (hbnd 0),hu,hbnd,?_,?_⟩
  · simpa only [heq] using hwt
  · intro v hv
    exact le_csSup hb ⟨v,hv,rfl⟩

lemma maximizing_limit {ν : Measure E} {R : ℝ≥0} {d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) :
    ∃ (φ : E → ℝ), NormalizedConvex R φ ∧
      Admissible ν R (dualOn (Metric.ball (0:E) R) φ) ∧
      ∀ v, Admissible ν R v → functional μ ν (Metric.ball (0:E) R) v ≤
        functional μ ν (Metric.ball (0:E) R) (dualOn (Metric.ball (0:E) R) φ) := by
  obtain ⟨u,M,hM,hu,hb,ha,hupper⟩ := maximizing_sequence μ hR hd hν
  obtain ⟨m,_,s,hs,hsm⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) M)).tendsto_subseq
    (fun n => ⟨integral_nonneg (hu n).nonneg,hb n⟩)
  obtain ⟨φ,t,hφ,ht,hpt⟩ := admissible_conjugate_subsequence hR (fun n => hu (s n))
  have hp (z : E) : Tendsto (fun n => conjugate (Metric.ball (0:E) R) (u (s (t n))) z)
      atTop (𝓝 (φ z)) := hpt.tendsto_comp hφ.lipschitz.continuous.continuousAt tendsto_const_nhds
  obtain ⟨had,hval⟩ := functional_limit_upper μ hR hd hM (fun n => hu (s (t n))) hν
    (fun n => hb (s (t n))) hφ hp (hsm.comp ht.tendsto_atTop)
      (ha.comp (hs.tendsto_atTop.comp ht.tendsto_atTop))
  exact ⟨φ,hφ,had,fun v hv => (hupper v hv).trans hval⟩

theorem exists_variational_maximizer {ν : Measure E} {R : ℝ≥0} {d : ℝ}
    (hR : 0 < R) (hd : 0 < d)
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) :
    ∃ u, Admissible ν R u ∧ ∀ v, Admissible ν R v →
      functional μ ν (Metric.ball (0:E) R) v ≤ functional μ ν (Metric.ball (0:E) R) u := by
  obtain ⟨φ,_,hu,hm⟩ := maximizing_limit μ hR hd hν
  exact ⟨_,hu,hm⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma even_convex_minimum {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) (he : Function.Even φ) (z : E) :
    φ 0 ≤ φ z := by
  have hh := hc.2 (mem_univ z) (mem_univ (-z)) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
  simp only [smul_neg,add_neg_cancel,smul_eq_mul,he z] at hh
  linarith

lemma conjugate_perturb_le {K : Set E} (hK : K.Nonempty) {u v : E → ℝ} {R m A : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hv : ∀ x ∈ K, m ≤ v x)
    (h : ∀ x ∈ K, v x-A ≤ u x) (z : E) : conjugate K u z ≤ conjugate K v z+A := by
  apply conjugate_le hK
  intro x hx
  have hh := le_conjugate hR hv hx z
  linarith [h x hx]

lemma conjugate_perturb_abs {K : Set E} (hK : K.Nonempty) {u v : E → ℝ} {R m A : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (h : ∀ x ∈ K, |v x-u x| ≤ A) (z : E) : |conjugate K v z-conjugate K u z| ≤ A := by
  have hv : ∀ x ∈ K, m-A ≤ v x := fun x hx => by
    have hh := (abs_le.mp (h x hx)).1
    linarith [hu x hx]
  apply abs_le.mpr
  constructor
  · have hh := conjugate_perturb_le (u:=u) (v:=v) (A:=A) hK hR hv (fun x hx => by linarith [(abs_le.mp (h x hx)).2]) z
    linarith
  · have hh := conjugate_perturb_le (u:=v) (v:=u) (A:=A) hK hR hu (fun x hx => by linarith [(abs_le.mp (h x hx)).1]) z
    linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalized_conjugate {R : ℝ≥0} {w : E → ℝ} {m : ℝ} (hR : 0 < R)
    (hw : ∀ x ∈ Metric.ball (0:E) R, m ≤ w x) (he : Function.Even w) :
    NormalizedConvex R (fun z => conjugate (Metric.ball (0:E) R) w z-conjugate (Metric.ball (0:E) R) w 0) := by
  have hK : (Metric.ball (0:E) (R:ℝ)).Nonempty := ⟨0,by simpa using hR⟩
  have hKR : ∀ x ∈ Metric.ball (0:E) (R:ℝ), ‖x‖ ≤ R :=
    fun x hx => (by simpa [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < R).le
  have hc := convexOn_conjugate hK hKR hw
  have he' := conjugate_even hK hKR hw
    (fun x hx => by simpa [Metric.mem_ball,dist_zero_right] using hx) he
  refine ⟨?_,sub_self _,fun z => sub_nonneg.mpr (even_convex_minimum hc he' z),
    fun z => by rw [he' z],?_⟩
  · simpa only [add_zero] using (conjugate_lipschitz hK hKR hw).sub (LipschitzWith.const (conjugate _ w 0))
  · refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    have hconst : (a+b)*conjugate (Metric.ball (0:E) R) w 0=conjugate (Metric.ball (0:E) R) w 0 := by rw [hab,one_mul]
    nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalized_conjugate_dual_bdd {R : ℝ≥0} {w : E → ℝ} {m : ℝ}
    (hw : ∀ x ∈ Metric.ball (0:E) R, m ≤ w x) :
    ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-
      (conjugate (Metric.ball (0:E) R) w z-conjugate (Metric.ball (0:E) R) w 0)) '' univ) := by
  intro x hx
  refine ⟨w x+conjugate (Metric.ball (0:E) R) w 0,?_⟩
  rintro _ ⟨z,_,rfl⟩
  have hh := le_conjugate (fun y hy =>
    (by simpa [Metric.mem_ball,dist_zero_right] using hy : ‖y‖ < (R:ℝ)).le) hw hx z
  rw [real_inner_comm z x] at hh
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalized_envelope_le {R : ℝ≥0} {w : E → ℝ} {m : ℝ} {x : E}
    (hw : ∀ x ∈ Metric.ball (0:E) R, m ≤ w x)
    (hx : x ∈ Metric.ball (0:E) R) :
    dualOn (Metric.ball (0:E) R) (fun z => conjugate (Metric.ball (0:E) R) w z-
      conjugate (Metric.ball (0:E) R) w 0) x ≤ w x+conjugate (Metric.ball (0:E) R) w 0 := by
  rw [dualOn_eq hx]
  apply conjugate_le univ_nonempty
  intro z _
  have hh := le_conjugate (fun y hy =>
    (by simpa [Metric.mem_ball,dist_zero_right] using hy : ‖y‖ < (R:ℝ)).le) hw hx z
  rw [real_inner_comm z x] at hh
  linarith

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma normalized_envelope_admissible {ν : Measure E} [IsProbabilityMeasure ν]
    {R : ℝ≥0} {w : E → ℝ} {m : ℝ} (hR : 0 < R)
    (hw : ∀ x ∈ Metric.ball (0:E) R, m ≤ w x) (he : Function.Even w)
    (hi : Integrable w ν) (hν : ∀ᵐ x ∂ν, x ∈ Metric.ball (0:E) R) :
    Admissible ν R (dualOn (Metric.ball (0:E) R) (fun z => conjugate (Metric.ball (0:E) R) w z-
      conjugate (Metric.ball (0:E) R) w 0)) := by
  let φ := fun z => conjugate (Metric.ball (0:E) R) w z-conjugate (Metric.ball (0:E) R) w 0
  have hφ : NormalizedConvex R φ := normalized_conjugate hR hw he
  have hb := normalized_conjugate_dual_bdd hw
  have hn := dualOn_nonneg hφ.zero hb
  have hc := convexOn_dualOn (convex_ball (0:E) (R:ℝ)) hb
  have ham : AEStronglyMeasurable (dualOn (Metric.ball (0:E) R) φ) ν :=
    (aestronglyMeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      ((ConvexOn.continuousOn Metric.isOpen_ball (convexOn_conjugate_of_bdd univ_nonempty
        (convex_ball (0:E) (R:ℝ)) hb)).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
  refine ⟨hc,hn,dualOn_zero hφ.zero hφ.nonneg hb,dualOn_even_ball hφ.even,
    fun x hx => indicator_of_notMem hx _,?_⟩
  apply (hi.add (integrable_const (conjugate (Metric.ball (0:E) R) w 0))).mono' ham
  filter_upwards [hν] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (hn x)]
  exact normalized_envelope_le hw hx

variable (μ : Measure E) [μ.IsAddHaarMeasure]
lemma normalized_envelope_functional_ge {ν : Measure E} [IsProbabilityMeasure ν]
    {R : ℝ≥0} {w : E → ℝ} {m : ℝ} (hR : 0 < R)
    (hw : ∀ x ∈ Metric.ball (0:E) R, m ≤ w x) (he : Function.Even w)
    (hi : Integrable w ν) (hν : ∀ᵐ x ∂ν, x ∈ Metric.ball (0:E) R)
    (hI : Integrable (fun z => Real.exp (-conjugate (Metric.ball (0:E) R) w z)) μ) :
    ∃ v, Admissible ν R v ∧ functional μ ν (Metric.ball (0:E) R) w ≤
      functional μ ν (Metric.ball (0:E) R) v := by
  let K := Metric.ball (0:E) (R:ℝ)
  let c := conjugate K w 0
  let φ := fun z => conjugate K w z-c
  let v := dualOn K φ
  have hφ : NormalizedConvex R φ := normalized_conjugate hR hw he
  have hb := normalized_conjugate_dual_bdd hw
  have hv : Admissible ν R v := normalized_envelope_admissible hR hw he hi hν
  have heq : conjugate K v=φ :=
    conjugate_dualOn_ball hR hφ.lipschitz hφ.zero hφ.nonneg hφ.convex hb
  have hIp : 0 < ∫ z, Real.exp (-conjugate K w z) ∂μ := integral_exp_pos hI
  have hIeq : (∫ z, Real.exp (-conjugate K v z) ∂μ)=
      Real.exp c*(∫ z,Real.exp (-conjugate K w z) ∂μ) := by
    rw [heq,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change Real.exp (-φ z)=Real.exp c*Real.exp (-conjugate K w z)
      rw [← Real.exp_add]
      congr 1
      dsimp only [φ]
      ring
  have hm : (∫ x,v x ∂ν) ≤ (∫ x,w x ∂ν)+c := by
    calc
      _ ≤ ∫ x,w x+c ∂ν := by
        apply integral_mono_ae hv.integrable (hi.add (integrable_const c))
        filter_upwards [hν] with x hx
        exact normalized_envelope_le hw hx
      _ = _ := by simp [integral_add hi (integrable_const c)]
  refine ⟨v,hv,?_⟩
  change Real.log (∫ z, Real.exp (-conjugate K w z) ∂μ)-(∫ x,w x ∂ν) ≤
    Real.log (∫ z, Real.exp (-conjugate K v z) ∂μ)-(∫ x,v x ∂ν)
  rw [hIeq,Real.log_mul (Real.exp_ne_zero c) hIp.ne',Real.log_exp]
  linarith

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma fenchel_gap_control {K : Set E} {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) {z g : E}
    (hd : HasFDerivAt (conjugate K u) (innerSL ℝ g) z) {ε : ℝ} (hε : 0 < ε) :
    ∃ h > 0, ∀ x ∈ K, ‖x-g‖ ≤ ε+(conjugate K u z+u x-⟪x,z⟫_ℝ)/h := by
  obtain ⟨δ,hδ,hδb⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε)
  refine ⟨δ/2,by positivity,?_⟩
  intro x hx
  have hgap : 0 ≤ conjugate K u z+u x-⟪x,z⟫_ℝ := by
    linarith [le_conjugate hR hu hx z]
  by_cases hzero : x-g=0
  · rw [hzero,norm_zero]
    positivity
  have hn : 0 < ‖x-g‖ := norm_pos_iff.mpr hzero
  let y := ((δ/2)/‖x-g‖) • (x-g)
  have hyn : ‖y‖=δ/2 := by
    dsimp only [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (by positivity) hn)]
    exact div_mul_cancel₀ _ hn.ne'
  have hyδ : dist (z+y) z < δ := by
    rw [dist_eq_norm,add_sub_cancel_left,hyn]
    linarith
  have hb := hδb hyδ
  change ‖conjugate K u (z+y)-conjugate K u z-(innerSL ℝ g) ((z+y)-z)‖ ≤ ε*‖(z+y)-z‖ at hb
  rw [add_sub_cancel_left,innerSL_apply_apply,hyn,Real.norm_eq_abs] at hb
  have hi : ⟪x-g,y⟫_ℝ=(δ/2)*‖x-g‖ := by
    dsimp only [y]
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  have hf := le_conjugate hR hu hx (z+y)
  rw [inner_add_right] at hf
  rw [inner_sub_left] at hi
  have hz := (abs_le.mp hb).2
  have hh : (δ/2)*‖x-g‖ ≤ conjugate K u z+u x-⟪x,z⟫_ℝ+ε*(δ/2) := by linarith
  calc
    _ ≤ (conjugate K u z+u x-⟪x,z⟫_ℝ+ε*(δ/2))/(δ/2) :=
      (le_div_iff₀ (show (0:ℝ)<δ/2 by positivity)).mpr (by nlinarith [hh])
    _ = _ := by field_simp; ring


omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma tilt_lower {K : Set E} {u f : E → ℝ} {m B t : ℝ}
    (hu : ∀ x ∈ K, m ≤ u x) (hf : ∀ x ∈ K, |f x| ≤ B) :
    ∀ x ∈ K, m-|t| *B ≤ u x+t*f x := by
  intro x hx
  have hs := neg_abs_le (t*f x)
  rw [abs_mul] at hs
  have hb := mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg t)
  linarith [hu x hx]

lemma tilted_conjugate_remainder_bound {K : Set E} (hK : K.Nonempty) {u f : E → ℝ}
    {R m B : ℝ} {C : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hf : LipschitzWith C f) (hB : ∀ x ∈ K, |f x| ≤ B) {z g : E} {ε h t : ℝ}
    (hh : 0 < h) (hgap : ∀ x ∈ K, ‖x-g‖ ≤ ε+(conjugate K u z+u x-⟪x,z⟫_ℝ)/h)
    (ht : |t| *(C:ℝ) ≤ h) :
    |conjugate K (fun x => u x+t*f x) z-conjugate K u z+t*f g| ≤ |t| *(C:ℝ)*ε := by
  let a := |t| *(C:ℝ)
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg t) C.coe_nonneg
  have ha1 : a/h ≤ 1 := (div_le_one hh).mpr ht
  have hg0 (x : E) (hx : x ∈ K) : 0 ≤ conjugate K u z+u x-⟪x,z⟫_ℝ := by
    linarith [le_conjugate hR hu hx z]
  have htlo := tilt_lower hu hB (t:=t)
  have hdist (x : E) (hx : x ∈ K) :
      |t*(f x-f g)| ≤ a*(ε+(conjugate K u z+u x-⟪x,z⟫_ℝ)/h) := by
    rw [abs_mul]
    have hf' : |f x-f g| ≤ (C:ℝ)*‖x-g‖ := by simpa only [Real.norm_eq_abs] using hf.norm_sub_le x g
    calc
      _ ≤ |t| *((C:ℝ)*‖x-g‖) := mul_le_mul_of_nonneg_left hf' (abs_nonneg t)
      _ = a*‖x-g‖ := by dsimp [a]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgap x hx) ha
  have hup : conjugate K (fun x => u x+t*f x) z ≤ conjugate K u z-t*f g+a*ε := by
    apply conjugate_le hK
    intro x hx
    have h1 := (abs_le.mp (hdist x hx)).1
    have h2 := mul_le_mul_of_nonneg_right ha1 (hg0 x hx)
    have heq : a*(ε+(conjugate K u z+u x-⟪x,z⟫_ℝ)/h)=
        a*ε+(a/h)*(conjugate K u z+u x-⟪x,z⟫_ℝ) := by ring
    rw [heq] at h1
    nlinarith
  have hden : 0 < 1+a/h := by positivity
  have hlow : conjugate K u z ≤
      (conjugate K (fun x => u x+t*f x) z+t*f g+a*ε+(a/h)*conjugate K u z)/(1+a/h) := by
    apply conjugate_le hK
    intro x hx
    apply (le_div_iff₀ hden).mpr
    have h1 := (abs_le.mp (hdist x hx)).2
    have h2 := le_conjugate hR htlo hx z
    have heq : a*(ε+(conjugate K u z+u x-⟪x,z⟫_ℝ)/h)=
        a*ε+(a/h)*(conjugate K u z+u x-⟪x,z⟫_ℝ) := by ring
    rw [heq] at h1
    nlinarith
  have hlow' := (le_div_iff₀ hden).mp hlow
  apply abs_le.mpr
  constructor <;> dsimp only [a] at * <;> nlinarith

lemma hasDerivAt_conjugate_tilt {K : Set E} (hK : K.Nonempty) {u f : E → ℝ}
    {R m B : ℝ} {C : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hf : LipschitzWith C f) (hB : ∀ x ∈ K, |f x| ≤ B) {z g : E}
    (hd : HasFDerivAt (conjugate K u) (innerSL ℝ g) z) :
    HasDerivAt (fun t : ℝ => conjugate K (fun x => u x+t*f x) z) (-f g) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hC : 0 < (C:ℝ)+1 := by positivity
  obtain ⟨h,hh,hgap⟩ := fenchel_gap_control hR hu hd (div_pos hε hC)
  refine Metric.eventually_nhds_iff.mpr ⟨h/((C:ℝ)+1),div_pos hh hC,?_⟩
  intro t ht
  have ht' : |t| *((C:ℝ)+1) < h := (lt_div_iff₀ hC).mp (by simpa [Real.dist_eq] using ht)
  have htC : |t| *(C:ℝ) ≤ h := by nlinarith [abs_nonneg t]
  have he := tilted_conjugate_remainder_bound hK hR hu hf hB hh hgap htC
  have hfrac : (C:ℝ)*(ε/((C:ℝ)+1)) ≤ ε := by
    calc
      _ = ((C:ℝ)*ε)/((C:ℝ)+1) := by ring
      _ ≤ ε := (div_le_iff₀ hC).mpr (by nlinarith)
  have heq : (fun t => conjugate K (fun x => u x+t*f x) z) 0=conjugate K u z := by simp
  change conjugate K (fun x => u x+0*f x) z=conjugate K u z at heq
  rw [heq]
  simp only [sub_zero,smul_eq_mul,Real.norm_eq_abs]
  have halg : conjugate K (fun x => u x+t*f x) z-conjugate K u z-t*(-f g)=
      conjugate K (fun x => u x+t*f x) z-conjugate K u z+t*f g := by ring
  rw [halg]
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hfrac (abs_nonneg t)])


lemma conjugate_tilt_lipschitz {K : Set E} (hK : K.Nonempty) {u f : E → ℝ}
    {R m B : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hB : ∀ x ∈ K, |f x| ≤ B) (z : E) (s t : ℝ) :
    |conjugate K (fun x => u x+t*f x) z-conjugate K (fun x => u x+s*f x) z| ≤ |t-s| *B := by
  apply conjugate_perturb_abs hK hR (tilt_lower hu hB)
  intro x hx
  have heq : u x+t*f x-(u x+s*f x)=(t-s)*f x := by ring
  rw [heq,abs_mul]
  exact mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg _)

lemma exp_sub_bound {x y A : ℝ} (hx : x ≤ A) (hy : y ≤ A) :
    |Real.exp x-Real.exp y| ≤ Real.exp A*|x-y| := by
  have hh := (convex_Iic A).norm_image_sub_le_of_norm_deriv_le
    (f:=Real.exp) (fun _ _ => Real.differentiableAt_exp)
    (fun b hb => by simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos b)] using Real.exp_le_exp.mpr hb) hy hx
  simpa only [Real.norm_eq_abs] using hh

lemma tilt_density_lipschitz {K : Set E} (hK : K.Nonempty) {u f : E → ℝ}
    {R m B : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hB : ∀ x ∈ K, |f x| ≤ B) (z : E) :
    LipschitzOnWith (Real.nnabs (Real.exp B*B*Real.exp (-conjugate K u z)))
      (fun t : ℝ => Real.exp (-conjugate K (fun x => u x+t*f x) z)) (Metric.ball 0 1) := by
  have hB0 : 0 ≤ B := by obtain ⟨x,hx⟩ := hK; exact (abs_nonneg _).trans (hB x hx)
  have hb (t : ℝ) (ht : t ∈ Metric.ball (0:ℝ) 1) :
      -conjugate K (fun x => u x+t*f x) z ≤ B-conjugate K u z := by
    have h := conjugate_tilt_lipschitz hK hR hu hB z 0 t
    simp only [zero_mul,add_zero,sub_zero] at h
    have ht' : |t| ≤ 1 := (by simpa [Metric.mem_ball,Real.dist_eq] using ht : |t| < 1).le
    have hb' := mul_le_mul_of_nonneg_right ht' hB0
    linarith [(abs_le.mp h).1]
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht s hs
  rw [Real.dist_eq,Real.dist_eq,Real.coe_nnabs]
  rw [abs_of_nonneg (show 0 ≤ Real.exp B*B*Real.exp (-conjugate K u z) by positivity)]
  calc
    _ ≤ Real.exp (B-conjugate K u z)*|(-conjugate K (fun x => u x+t*f x) z)-(-conjugate K (fun x => u x+s*f x) z)| :=
      exp_sub_bound (hb t ht) (hb s hs)
    _ = Real.exp (B-conjugate K u z)*|conjugate K (fun x => u x+t*f x) z-conjugate K (fun x => u x+s*f x) z| := by
      congr 1
      rw [neg_sub_neg,abs_sub_comm]
    _ ≤ Real.exp (B-conjugate K u z)*(|t-s| *B) :=
      mul_le_mul_of_nonneg_left (conjugate_tilt_lipschitz hK hR hu hB z s t) (Real.exp_pos _).le
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma hasDerivAt_tilt_partition {μ : Measure E} {K : Set E} (hK : K.Nonempty) {u f : E → ℝ}
    {R C : ℝ≥0} {m B : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hf : LipschitzWith C f) (hB : ∀ x ∈ K, |f x| ≤ B) {g : E → E}
    (hg : Measurable g) (hd : ∀ᵐ z ∂μ, HasFDerivAt (conjugate K u) (innerSL ℝ (g z)) z)
    (hI : Integrable (fun z => Real.exp (-conjugate K u z)) μ) :
    Integrable (fun z => f (g z)*Real.exp (-conjugate K u z)) μ ∧
    HasDerivAt (fun t : ℝ => ∫ z, Real.exp (-conjugate K (fun x => u x+t*f x) z) ∂μ)
      (∫ z, f (g z)*Real.exp (-conjugate K u z) ∂μ) 0 := by
  have hc := (conjugate_lipschitz hK hR hu).continuous
  apply hasDerivAt_integral_of_dominated_loc_of_lip (bound:=fun z => Real.exp B*B*Real.exp (-conjugate K u z))
    (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ)<1))
  · exact Eventually.of_forall fun t => ((conjugate_lipschitz hK hR (tilt_lower hu hB (t:=t))).continuous.neg.rexp).aestronglyMeasurable
  · simpa using hI
  · exact ((hf.continuous.measurable.comp hg).mul hc.neg.rexp.measurable).aestronglyMeasurable
  · exact Eventually.of_forall (tilt_density_lipschitz hK hR hu hB)
  · exact hI.const_mul _
  · filter_upwards [hd] with z hz
    have h := (hasDerivAt_conjugate_tilt hK hR hu hf hB hz).neg.exp
    simpa [mul_comm] using h

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma tilt_partition_integrable {μ : Measure E} {K : Set E} (hK : K.Nonempty) {u f : E → ℝ}
    {R : ℝ≥0} {m B : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x)
    (hB : ∀ x ∈ K, |f x| ≤ B)
    (hI : Integrable (fun z => Real.exp (-conjugate K u z)) μ) (t : ℝ) :
    Integrable (fun z => Real.exp (-conjugate K (fun x => u x+t*f x) z)) μ := by
  have hb (z : E) := (abs_le.mp (conjugate_tilt_lipschitz hK hR hu hB z 0 t)).1
  simp only [zero_mul,add_zero,sub_zero] at hb
  apply (hI.const_mul (Real.exp (|t| *B))).mono'
    (conjugate_lipschitz hK hR (tilt_lower hu hB (t:=t))).continuous.neg.rexp.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -conjugate K (fun x => u x+t*f x) z ≤ |t| *B-conjugate K u z
    have hbz : -(|t| *B) ≤ conjugate K (fun x => u x+t*f x) z-conjugate K u z := hb z
    linarith

lemma measurable_gradient (φ : E → ℝ) : Measurable (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma admissible_tail {ν : Measure E} {R : ℝ≥0} {d : ℝ} {u : E → ℝ}
    (hR : 0 < R) (hd : 0 < d) (hu : Admissible ν R u)
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) :
    ∃ c > 0, ∀ z, c*‖z‖-1 ≤ conjugate (Metric.ball (0:E) R) u z := by
  have hR' : (0:ℝ)<R := hR
  have hr : (0:ℝ)<(R:ℝ)/4 := by positivity
  have hm : 0 ≤ ∫ y,u y ∂ν := integral_nonneg hu.nonneg
  have hC := mul_pos hd (ball_real_pos μ hr)
  refine ⟨(R:ℝ)/4/((∫ y,u y ∂ν)/(d*μ.real (Metric.closedBall (0:E) ((R:ℝ)/4)))+1),by positivity,?_⟩
  exact mean_conjugate_lower_ball μ hr (S:=(R:ℝ)/2) (by linarith) (by linarith) hd ν hu
    (hν _ (by positivity) (by linarith))

lemma admissible_partition_integrable {ν : Measure E} {R : ℝ≥0} {d : ℝ} {u : E → ℝ}
    (hR : 0 < R) (hd : 0 < d) (hu : Admissible ν R u)
    (hν : ∀ S : ℝ, 0 ≤ S → S < R → ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ ν) :
    Integrable (fun z => Real.exp (-conjugate (Metric.ball (0:E) R) u z)) μ := by
  obtain ⟨c,hc,hl⟩ := admissible_tail μ hR hd hu hν
  exact tail_integrable μ (admissible_conjugate_lipschitz hR hu).continuous hc hl

lemma maximal_functional_tilt_le {ν : Measure E} [IsProbabilityMeasure ν]
    {R C : ℝ≥0} {u f : E → ℝ} {B : ℝ} (hR : 0 < R) (hu : Admissible ν R u)
    (hmax : ∀ v, Admissible ν R v → functional μ ν (Metric.ball (0:E) R) v ≤ functional μ ν (Metric.ball (0:E) R) u)
    (hν : ∀ᵐ x ∂ν, x ∈ Metric.ball (0:E) R)
    (hf : LipschitzWith C f) (he : Function.Even f) (hB : ∀ x ∈ Metric.ball (0:E) R, |f x| ≤ B)
    (hI : Integrable (fun z => Real.exp (-conjugate (Metric.ball (0:E) R) u z)) μ) (t : ℝ) :
    functional μ ν (Metric.ball (0:E) R) (fun x => u x+t*f x) ≤ functional μ ν (Metric.ball (0:E) R) u := by
  have hKR : ∀ x ∈ Metric.ball (0:E) (R:ℝ), ‖x‖ ≤ R :=
    fun x hx => (by simpa [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < R).le
  have hfi : Integrable f ν := (integrable_const B).mono' hf.continuous.aestronglyMeasurable
    (hν.mono fun x hx => by simpa only [Real.norm_eq_abs] using hB x hx)
  obtain ⟨v,hv,hvge⟩ := normalized_envelope_functional_ge μ hR
    (tilt_lower (fun x _ => hu.nonneg x) hB (t:=t))
    (fun x => by simp only [hu.even x,he x]) (hu.integrable.add (hfi.const_mul t)) hν
    (tilt_partition_integrable ⟨0,by simpa using hR⟩ hKR (fun x _ => hu.nonneg x) hB hI t)
  exact hvge.trans (hmax v hv)

lemma first_variation_even {ν : Measure E} [IsProbabilityMeasure ν]
    {R C : ℝ≥0} {u f : E → ℝ} {B : ℝ} (hR : 0 < R) (hu : Admissible ν R u)
    (hmax : ∀ v, Admissible ν R v → functional μ ν (Metric.ball (0:E) R) v ≤ functional μ ν (Metric.ball (0:E) R) u)
    (hν : ∀ᵐ x ∂ν, x ∈ Metric.ball (0:E) R)
    (hf : LipschitzWith C f) (he : Function.Even f) (hB : ∀ x ∈ Metric.ball (0:E) R, |f x| ≤ B)
    (hI : Integrable (fun z => Real.exp (-conjugate (Metric.ball (0:E) R) u z)) μ) :
    (∫ z, f (gradient (conjugate (Metric.ball (0:E) R) u) z)*Real.exp (-conjugate (Metric.ball (0:E) R) u z) ∂μ) /
      (∫ z, Real.exp (-conjugate (Metric.ball (0:E) R) u z) ∂μ) = ∫ x,f x ∂ν := by
  let K := Metric.ball (0:E) (R:ℝ)
  let φ := conjugate K u
  let I := ∫ z,Real.exp (-φ z) ∂μ
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R :=
    fun x hx => (by simpa [K,Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < R).le
  have hl : LipschitzWith R φ := admissible_conjugate_lipschitz hR hu
  have hdiff : ∀ᵐ z ∂μ, HasFDerivAt φ (innerSL ℝ (gradient φ z)) z := by
    filter_upwards [hl.ae_differentiableAt (μ:=μ)] with z hz
    exact hz.hasGradientAt.hasFDerivAt
  obtain ⟨_,hIp⟩ := hasDerivAt_tilt_partition ⟨0,by simpa [K] using hR⟩ hKR
    (fun x _ => hu.nonneg x) hf hB (measurable_gradient φ) hdiff hI
  have hIpos : 0 < I := integral_exp_pos hI
  have hfi : Integrable f ν := (integrable_const B).mono' hf.continuous.aestronglyMeasurable
    (hν.mono fun x hx => by simpa only [Real.norm_eq_abs] using hB x hx)
  have hzero : (∫ z, Real.exp (-conjugate K (fun x => u x+(0:ℝ)*f x) z) ∂μ)=I := by simp [I,φ]
  have hmean : HasDerivAt (fun t : ℝ => ∫ x,u x+t*f x ∂ν) (∫ x,f x ∂ν) 0 := by
    have heq : (fun t : ℝ => ∫ x,u x+t*f x ∂ν)=(fun t => (∫ x,u x ∂ν)+t*(∫ x,f x ∂ν)) := by
      funext t
      rw [integral_add hu.integrable (hfi.const_mul t),integral_const_mul]
    rw [heq]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (∫ x,f x ∂ν)).const_add (∫ x,u x ∂ν)
  have hp := (hIp.log (by rw [hzero]; exact hIpos.ne')).sub hmean
  have hloc : IsLocalMax (fun t : ℝ => functional μ ν K (fun x => u x+t*f x)) 0 := by
    apply Eventually.of_forall
    intro t
    simpa only [zero_mul,add_zero] using maximal_functional_tilt_le μ hR hu hmax hν hf he hB hI t
  have hstat := hloc.hasDerivAt_eq_zero hp
  rw [hzero] at hstat
  exact sub_eq_zero.mp hstat

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradient_odd_of_even {φ : E → ℝ} (he : Function.Even φ) :
    Function.Odd (gradient φ) := by
  intro z
  have heq : φ ∘ (ContinuousLinearEquiv.neg ℝ (M:=E))=φ := funext he
  have hh := (ContinuousLinearEquiv.neg ℝ (M:=E)).comp_right_fderiv (f:=φ) (x:=z)
  rw [heq] at hh
  have hd : fderiv ℝ φ (-z) = -fderiv ℝ φ z := by
    ext v
    have hp := congrArg (fun L : E →L[ℝ] ℝ => L v) hh
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.neg_apply, map_neg] at hp
    simpa using (congrArg Neg.neg hp).symm
  simp only [gradient,hd,map_neg]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma measure_ext_bounded_lipschitz {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : E → ℝ) (C : ℝ≥0) (B : ℝ), LipschitzWith C f → (∀ x, |f x| ≤ B) →
      (∫ x,f x ∂μ)=(∫ x,f x ∂ν)) : μ=ν := by
  have hcl (s : Set E) (hs : IsClosed s) : μ s=ν s := by
    let fs (n : ℕ) (x : E) : ℝ := thickenedIndicator (δ:=(1:ℝ)/(n+1)) (by positivity) s x
    have hfs (n : ℕ) : (∫ x,fs n x ∂μ)=(∫ x,fs n x ∂ν) := by
      apply h (fs n) _ 1
      · exact lipschitzWith_thickenedIndicator (by positivity) s
      · intro x
        dsimp only [fs]
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast thickenedIndicator_le_one (δ:=(1:ℝ)/(n+1)) (by positivity) s x
    have hμ := tendsto_integral_thickenedIndicator_of_isClosed μ hs
      (δs:=fun n : ℕ => (1:ℝ)/(n+1)) (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    have hν := tendsto_integral_thickenedIndicator_of_isClosed ν hs
      (δs:=fun n : ℕ => (1:ℝ)/(n+1)) (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    change Tendsto (fun n => ∫ x,fs n x ∂μ) atTop (𝓝 (μ.real s)) at hμ
    change Tendsto (fun n => ∫ x,fs n x ∂ν) atTop (𝓝 (ν.real s)) at hν
    simp_rw [hfs] at hμ
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp
      (tendsto_nhds_unique hμ hν)
  apply MeasureTheory.ext_of_generate_finite {s | IsClosed s}
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    (fun s hs => hcl s hs) (hcl univ isClosed_univ)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma first_variation_bounded {ν : Measure E} [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    {R C : ℝ≥0} {u f : E → ℝ} {B : ℝ} (hR : 0 < R) (hu : Admissible ν R u)
    (hmax : ∀ v, Admissible ν R v → functional μ ν (Metric.ball (0:E) R) v ≤ functional μ ν (Metric.ball (0:E) R) u)
    (hν : ∀ᵐ x ∂ν, x ∈ Metric.ball (0:E) R)
    (hf : LipschitzWith C f) (hB : ∀ x, |f x| ≤ B)
    (hI : Integrable (fun z => Real.exp (-conjugate (Metric.ball (0:E) R) u z)) μ) :
    (∫ z, f (gradient (conjugate (Metric.ball (0:E) R) u) z)*Real.exp (-conjugate (Metric.ball (0:E) R) u z) ∂μ) /
      (∫ z, Real.exp (-conjugate (Metric.ball (0:E) R) u z) ∂μ) = ∫ x,f x ∂ν := by
  let φ := conjugate (Metric.ball (0:E) R) u
  let g := gradient φ
  let fs := fun x => f x+f (-x)
  have hφe : Function.Even φ := (admissible_conjugate_normalized hR hu).even
  have hg : Function.Odd g := gradient_odd_of_even hφe
  have hgmeas : Measurable g := measurable_gradient φ
  have hρc := (admissible_conjugate_lipschitz hR hu).continuous.neg.rexp
  have hfN : LipschitzWith C (fun x : E => f (-x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_neg_neg] using hf.dist_le_mul (-x) (-y)
  have hfs : LipschitzWith (C+C) fs := hf.add hfN
  have hfse : Function.Even fs := fun x => by simp [fs,add_comm]
  have hfsB (x : E) : |fs x| ≤ 2*B := (abs_add_le _ _).trans (by linarith [hB x,hB (-x)])
  have hs := first_variation_even μ hR hu hmax hν hfs hfse (fun x _ => hfsB x) hI
  have hfi : Integrable f ν := (integrable_const B).mono' hf.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hfig : Integrable (fun z => f (g z)*Real.exp (-φ z)) μ := by
    apply (hI.const_mul B).mono' (((hf.continuous.measurable.comp hgmeas).mul hρc.measurable).aestronglyMeasurable)
    exact Eventually.of_forall fun z => by
      change ‖f (g z)*Real.exp (-φ z)‖ ≤ _
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
  have hfigN : Integrable (fun z => f (-g z)*Real.exp (-φ z)) μ := by
    simpa only [show ∀ x, g (-x) = -g x from hg, show ∀ x, φ (-x) = φ x from hφe] using hfig.comp_neg
  have hsμ : (∫ z,fs (g z)*Real.exp (-φ z) ∂μ)=2*(∫ z,f (g z)*Real.exp (-φ z) ∂μ) := by
    simp only [fs,add_mul]
    rw [integral_add hfig hfigN]
    have hn := integral_neg_eq_self (fun z => f (g z)*Real.exp (-φ z)) μ
    simp only [show ∀ x, g (-x) = -g x from hg, show ∀ x, φ (-x) = φ x from hφe] at hn
    rw [hn]
    ring
  have hsν : (∫ x,fs x ∂ν)=2*(∫ x,f x ∂ν) := by
    dsimp only [fs]
    rw [integral_add hfi hfi.comp_neg,integral_neg_eq_self]
    ring
  change (∫ z,fs (g z)*Real.exp (-φ z) ∂μ)/(∫ z,Real.exp (-φ z) ∂μ)=∫ x,fs x ∂ν at hs
  rw [hsμ,hsν,mul_div_assoc] at hs
  change (∫ z,f (g z)*Real.exp (-φ z) ∂μ)/(∫ z,Real.exp (-φ z) ∂μ)=_
  linarith

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma normalizedSource_probability {φ : E → ℝ}
    (hI : Integrable (fun z => Real.exp (-φ z)) μ) :
    IsProbabilityMeasure (normalizedSource μ φ) := by
  have hIp := integral_exp_pos hI
  apply isProbabilityMeasure_iff.mpr
  rw [normalizedSource,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · simp only [integral_div,div_self hIp.ne',ENNReal.ofReal_one]
  · exact hI.div_const _
  · exact Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hIp.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma integral_normalizedSource {φ : E → ℝ} (hφ : Measurable φ)
    (hI : Integrable (fun z => Real.exp (-φ z)) μ) (f : E → ℝ) :
    (∫ z,f z ∂normalizedSource μ φ) =
      (∫ z,f z*Real.exp (-φ z) ∂μ)/(∫ z,Real.exp (-φ z) ∂μ) := by
  have hIp := integral_exp_pos hI
  have hd : Measurable (fun z => ENNReal.ofReal (Real.exp (-φ z)/(∫ y,Real.exp (-φ y) ∂μ))) :=
    (hφ.neg.exp.div_const _).ennreal_ofReal
  rw [normalizedSource,integral_withDensity_eq_integral_toReal_smul hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hIp.le),smul_eq_mul]
  rw [← integral_div]
  congr 1
  funext z
  ring

lemma maximizer_pushforward {ν : Measure E} [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    {R : ℝ≥0} {u : E → ℝ} (hR : 0 < R) (hu : Admissible ν R u)
    (hmax : ∀ v, Admissible ν R v → functional μ ν (Metric.ball (0:E) R) v ≤ functional μ ν (Metric.ball (0:E) R) u)
    (hν : ∀ᵐ x ∂ν, x ∈ Metric.ball (0:E) R)
    (hI : Integrable (fun z => Real.exp (-conjugate (Metric.ball (0:E) R) u z)) μ) :
    Measure.map (gradient (conjugate (Metric.ball (0:E) R) u))
      (normalizedSource μ (conjugate (Metric.ball (0:E) R) u)) = ν := by
  let φ := conjugate (Metric.ball (0:E) R) u
  let : IsProbabilityMeasure (normalizedSource μ φ) := normalizedSource_probability μ hI
  have hg := measurable_gradient φ
  let : IsProbabilityMeasure (Measure.map (gradient φ) (normalizedSource μ φ)) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  apply measure_ext_bounded_lipschitz
  intro f C B hf hB
  rw [integral_map hg.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_normalizedSource μ (admissible_conjugate_lipschitz hR hu).continuous.measurable hI]
  exact first_variation_bounded μ hR hu hmax hν hf hB hI

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace TruncatedMoment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integrable_density {V : E → ℝ} (hV : Continuous V) (R : ℝ) :
    IntegrableOn (fun x => Real.exp (-V x)) (Metric.ball (0:E) R) μ :=
  ((hV.neg.rexp.continuousOn).integrableOn_compact (isCompact_closedBall (0:E) R)).mono_set
    Metric.ball_subset_closedBall

lemma partition_pos {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0 < R) :
    0 < partition μ R V := by
  let : NeZero (μ.restrict (Metric.ball (0:E) R)) := ⟨by
    intro he
    have hh := congrArg (fun m : Measure E => m univ) he
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.coe_zero,Pi.zero_apply] at hh
    exact (Metric.measure_ball_pos μ 0 hR).ne' hh⟩
  exact integral_exp_pos (integrable_density μ hV R)

lemma probability {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (target μ R V) := by
  have hZ := partition_pos μ hV hR
  apply isProbabilityMeasure_iff.mpr
  rw [target,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div]
    change ENNReal.ofReal (partition μ R V / partition μ R V) = 1
    rw [div_self hZ.ne',ENNReal.ofReal_one]
  · exact (integrable_density μ hV R).div_const _
  · exact Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma ae_mem_ball (V : E → ℝ) (R : ℝ) :
    ∀ᵐ x ∂target μ R V, x ∈ Metric.ball (0:E) R :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)

lemma density_lower {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0 < R) :
    ∃ d > 0, ∀ S : ℝ, 0 ≤ S → S < R →
      ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) S) ≤ target μ R V := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:E) R).bddAbove_image hV.continuousOn
  let d := Real.exp (-M)/partition μ R V
  have hZ := partition_pos μ hV hR
  have hd : 0 < d := div_pos (Real.exp_pos _) hZ
  refine ⟨d,hd,fun S _ hSR => ?_⟩
  have hsub : Metric.closedBall (0:E) S ⊆ Metric.ball (0:E) R := by
    intro x hx
    exact (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hSR))
  have hl : ENNReal.ofReal d • μ.restrict (Metric.ball (0:E) R) ≤ target μ R V := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ hZ.le
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (hM (mem_image_of_mem _ (Metric.ball_subset_closedBall hx)))
  apply le_trans _ hl
  intro s
  simp only [Measure.smul_apply,smul_eq_mul]
  gcongr

lemma even_density_measure {w : E → ℝ≥0∞} (hw : Function.Even w) :
    (μ.withDensity w).IsNegInvariant := by
  constructor
  apply Measure.ext
  intro s hs
  rw [Measure.neg_apply,withDensity_apply _ hs.neg,withDensity_apply _ hs]
  rw [← lintegral_indicator hs.neg,← lintegral_indicator hs]
  have heq : (fun x => (-s).indicator w x)=(fun x => s.indicator w (-x)) := by
    funext x
    by_cases hx : -x ∈ s
    · simp [Set.mem_neg,hx,show w (-x)=w x from hw x]
    · simp [Set.mem_neg,hx]
  rw [heq,lintegral_neg_eq_self]

lemma negInvariant {V : E → ℝ} (hV : Function.Even V) (R : ℝ) :
    (target μ R V).IsNegInvariant := by
  rw [target,← withDensity_indicator measurableSet_ball]
  apply even_density_measure μ
  intro x
  by_cases hx : x ∈ Metric.ball (0:E) R
  · have hnx : -x ∈ Metric.ball (0:E) R := by simpa [Metric.mem_ball,dist_zero_right] using hx
    simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hnx,show V (-x)=V x from hV x]
  · have hnx : -x ∉ Metric.ball (0:E) R := by simpa [Metric.mem_ball,dist_zero_right] using hx
    simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem hnx]

end TruncatedMoment

namespace CompactMomentVariational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gradient_add_constant [CompleteSpace E] (φ : E → ℝ) (a : ℝ) :
    gradient (fun z => φ z + a) = gradient φ := by
  funext z
  simp only [gradient,fderiv_add_const]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma source_shift {φ : E → ℝ}
    (hI : Integrable (fun z => Real.exp (-φ z)) μ) :
    μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-(φ z + Real.log (∫ y,Real.exp (-φ y) ∂μ))))) =
      normalizedSource μ φ := by
  congr 1
  funext z
  congr 1
  rw [neg_add,Real.exp_add,Real.exp_neg (Real.log _),Real.exp_log (integral_exp_pos hI),div_eq_mul_inv]

end CompactMomentVariational
end

open scoped ENNReal

noncomputable section
namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma fenchel_eq_at_gradient {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {z : E}
    (hd : DifferentiableAt ℝ φ z) :
    conjugate univ φ (gradient φ z) = ⟪gradient φ z,z⟫_ℝ-φ z := by
  have hb : BddAbove ((fun w => ⟪w,gradient φ z⟫_ℝ-φ w) '' univ) := by
    refine ⟨⟪gradient φ z,z⟫_ℝ-φ z,?_⟩
    rintro _ ⟨w,_,rfl⟩
    have hh := convex_supporting_gradient hc hd w
    rw [inner_sub_right] at hh
    dsimp only
    rw [real_inner_comm (gradient φ z) w]
    linarith
  apply le_antisymm
  · apply conjugate_le (Set.univ_nonempty)
    intro w _
    have hh := convex_supporting_gradient hc hd w
    rw [inner_sub_right] at hh
    rw [real_inner_comm (gradient φ z) w]
    linarith
  · simpa only [conjugate,real_inner_comm (gradient φ z) z] using
      (le_csSup hb (mem_image_of_mem (fun w => ⟪w,gradient φ z⟫_ℝ-φ w) (mem_univ z)))

lemma inverse_gradient {φ : E → ℝ} {K : Set E} (hK : IsOpen K)
    (hc : ConvexOn ℝ univ φ) {z : E} (hd : DifferentiableAt ℝ φ z)
    (hg : gradient φ z ∈ K)
    (hb : ∀ x ∈ K, BddAbove ((fun w => ⟪w,x⟫_ℝ-φ w) '' univ))
    (hu : DifferentiableAt ℝ (dualOn K φ) (gradient φ z)) :
    gradient (dualOn K φ) (gradient φ z) = z := by
  let x := gradient φ z
  have he : dualOn K φ x = ⟪z,x⟫_ℝ-φ z := by
    rw [dualOn_eq hg,fenchel_eq_at_gradient hc hd,real_inner_comm]
  have hmin : IsLocalMin (fun y => dualOn K φ y-⟪z,y⟫_ℝ) x := by
    filter_upwards [hK.mem_nhds hg] with y hy
    have hh := fenchel_dualOn hb hy z
    rw [he,real_inner_comm y z] at *
    linarith
  have hz := hmin.hasFDerivAt_eq_zero
    (hu.hasFDerivAt.sub (innerSL ℝ z).hasFDerivAt)
  have hz' : fderiv ℝ (dualOn K φ) x = innerSL ℝ z := sub_eq_zero.mp hz
  rw [gradient,hz']
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply z

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma locallyLipschitz_ae_differentiable {μ : Measure E} [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsOpen K) {f : E → ℝ} (hf : LocallyLipschitzOn K f) :
    ∀ᵐ x ∂μ, x ∈ K → DifferentiableAt ℝ f x := by
  have hloc : ∀ x ∈ K, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ≥0, LipschitzOnWith C f U := by
    intro x hx
    obtain ⟨C,t,ht,hft⟩ := hf hx
    rw [hK.nhdsWithin_eq hx] at ht
    exact ⟨interior t,isOpen_interior,mem_interior_iff_mem_nhds.mpr ht,C,
      hft.mono interior_subset⟩
  choose U hUo hUx C hC using hloc
  obtain ⟨t,ht,hcover⟩ := (HereditarilyLindelofSpace.isLindelof K).elim_nhds_subcover' U
    (fun x hx => (hUo x hx).mem_nhds (hUx x hx))
  have hh : ∀ᵐ x ∂μ.restrict (⋃ z ∈ t, U z.val z.property), DifferentiableAt ℝ f x := by
    rw [ae_restrict_biUnion_iff _ ht]
    intro z _
    rw [ae_restrict_iff' (hUo z.val z.property).measurableSet]
    filter_upwards [(hC z.val z.property).ae_differentiableWithinAt_of_mem (μ:=μ)] with x hx
    intro hxU
    exact (hx hxU).differentiableAt ((hUo z.val z.property).mem_nhds hxU)
  rw [← ae_restrict_iff' hK.measurableSet]
  exact (ae_mono (Measure.restrict_mono hcover le_rfl)) hh

lemma convex_ae_differentiable {μ : Measure E} [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsOpen K) {f : E → ℝ} (hf : ConvexOn ℝ K f) :
    ∀ᵐ x ∂μ, x ∈ K → DifferentiableAt ℝ f x :=
  locallyLipschitz_ae_differentiable hK (hf.locallyLipschitzOn hK)


lemma gradient_measurable (φ : E → ℝ) : Measurable (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)

theorem weak_inverse {μ σ ν : Measure E} [μ.IsAddHaarMeasure]
    (hσ : σ ≪ μ) (hν : ν ≪ μ) {K : Set E} (hK : IsOpen K) (hcK : Convex ℝ K)
    {φ : E → ℝ} {R : ℝ≥0} (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ K, BddAbove ((fun w => ⟪w,x⟫_ℝ-φ w) '' univ))
    (hs : ∀ᵐ x ∂ν, x ∈ K) (hm : Measure.map (gradient φ) σ = ν) :
    ∀ᵐ z ∂σ, gradient (dualOn K φ) (gradient φ z) = z := by
  have hd : ∀ᵐ x ∂ν, x ∈ K → DifferentiableAt ℝ (dualOn K φ) x :=
    hν.ae_le (convex_ae_differentiable hK (convexOn_dualOn hcK hb))
  have hg : ∀ᵐ x ∂ν, x ∈ K ∧ DifferentiableAt ℝ (dualOn K φ) x := by
    filter_upwards [hs,hd] with x hx hh
    exact ⟨hx,hh hx⟩
  rw [← hm] at hg
  have hg' := ae_of_ae_map (gradient_measurable φ).aemeasurable hg
  filter_upwards [hσ.ae_le (hl.ae_differentiableAt (μ:=μ)),hg'] with z hz hg
  exact inverse_gradient hK hc hz hg.1 hb hg.2

theorem reverse_pushforward {μ σ ν : Measure E} [μ.IsAddHaarMeasure]
    (hσ : σ ≪ μ) (hν : ν ≪ μ) {K : Set E} (hK : IsOpen K) (hcK : Convex ℝ K)
    {φ : E → ℝ} {R : ℝ≥0} (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ K, BddAbove ((fun w => ⟪w,x⟫_ℝ-φ w) '' univ))
    (hs : ∀ᵐ x ∂ν, x ∈ K) (hm : Measure.map (gradient φ) σ = ν) :
    Measure.map (gradient (dualOn K φ)) ν = σ := by
  rw [← hm,Measure.map_map (gradient_measurable _) (gradient_measurable _)]
  have he := weak_inverse hσ hν hK hcK hc hl hb hs hm
  exact (Measure.map_congr he).trans Measure.map_id

end

section

lemma map_density_pullback {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (σ : Measure α) {g : α → β} (hg : Measurable g) {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map g (σ.withDensity (w ∘ g)) = (Measure.map g σ).withDensity w := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hg hs,withDensity_apply _ (hs.preimage hg),withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage hg),← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hg]
  congr 1

lemma reverse_weighted {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {σ : Measure α} {ν : Measure β} {g : α → β} {f : β → α}
    (hg : Measurable g) (hf : Measurable f)
    (hm : Measure.map g σ = ν) (hi : ∀ᵐ z ∂σ, f (g z)=z)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map f (ν.withDensity w) = σ.withDensity (w ∘ g) := by
  rw [← hm,← map_density_pullback σ hg hw,Measure.map_map hf hg]
  exact (Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le hi)).trans Measure.map_id

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma dual_conjugate_bdd {K : Set E} {u : E → ℝ} {R m : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hu : ∀ x ∈ K, m ≤ u x) {x : E} (hx : x ∈ K) :
    BddAbove ((fun z => ⟪z,x⟫_ℝ-conjugate K u z) '' univ) := by
  refine ⟨u x,?_⟩
  rintro _ ⟨z,_,rfl⟩
  have hh := le_conjugate hR hu hx z
  dsimp only
  rw [real_inner_comm z x] at hh
  linarith

lemma dual_add_constant_bdd {φ : E → ℝ} {x : E}
    (hb : BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) (a : ℝ) :
    BddAbove ((fun z => ⟪z,x⟫_ℝ-(φ z+a)) '' univ) := by
  obtain ⟨b,hb⟩ := hb
  refine ⟨b-a,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  have hh := hb (mem_image_of_mem (fun z => ⟪z,x⟫_ℝ-φ z) hz)
  dsimp only at *
  linarith

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem weak_MA_of_transport {V φ : E → ℝ} (hV : Continuous V)
    {R : ℝ≥0} (hR : 0 < R) (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      TruncatedMoment.target μ R V) :
    Measure.map (gradient (dualOn (Metric.ball (0:E) R) φ)) (μ.restrict (Metric.ball (0:E) R)) =
      μ.withDensity (fun z => ENNReal.ofReal
        (TruncatedMoment.partition μ R V * Real.exp (V (gradient φ z)-φ z))) := by
  let K := Metric.ball (0:E) (R:ℝ)
  let Z := TruncatedMoment.partition μ R V
  let w := fun x => ENNReal.ofReal (Real.exp (-V x)/Z)
  let σ := μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))
  let ν := TruncatedMoment.target μ R V
  have hZ : 0 < Z := TruncatedMoment.partition_pos μ hV hR
  have hw : Measurable w := (hV.neg.rexp.measurable.div_const Z).ennreal_ofReal
  have hσ : σ ≪ μ := withDensity_absolutelyContinuous _ _
  have hν : ν ≪ μ := (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hi := weak_inverse hσ hν Metric.isOpen_ball (convex_ball (0:E) R) hc hl hb
    (TruncatedMoment.ae_mem_ball μ V R) hm
  have hinv : ν.withDensity (fun x => (w x)⁻¹) = μ.restrict K := by
    apply withDensity_inv_same₀ hw.aemeasurable
    · exact Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (div_pos (Real.exp_pos _) hZ)
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  rw [← hinv]
  have hr := reverse_weighted (gradient_measurable _) (gradient_measurable _) hm hi
    (show Measurable (fun x => (w x)⁻¹) from hw.inv)
  exact hr.trans (by
    change σ.withDensity (fun z => (w (gradient φ z))⁻¹) = _
    dsimp only [σ]
    refine (withDensity_mul μ
      (show Measurable (fun z => ENNReal.ofReal (Real.exp (-φ z))) from
        hl.continuous.neg.rexp.measurable.ennreal_ofReal)
      (show Measurable (fun z => (w (gradient φ z))⁻¹) from
        hw.inv.comp (gradient_measurable φ))).symm.trans ?_
    congr 1
    funext z
    dsimp only [Pi.mul_apply,w]
    rw [← ENNReal.ofReal_inv_of_pos (div_pos (Real.exp_pos _) hZ),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simp only [Real.exp_neg,inv_div,div_inv_eq_mul,Real.exp_sub]
    ring)

theorem exists_weak_truncated_MA {V : E → ℝ} (hV : Continuous V) (hVe : Function.Even V)
    {R : ℝ≥0} (hR : 0 < R) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Function.Even φ ∧ LipschitzWith R φ ∧
      (∃ c > 0, ∃ b : ℝ, ∀ z, c*‖z‖-b ≤ φ z) ∧
      IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) ∧
      (∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) ∧
      Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
        TruncatedMoment.target μ R V ∧
      Measure.map (gradient (dualOn (Metric.ball (0:E) R) φ)) (μ.restrict (Metric.ball (0:E) R)) =
        μ.withDensity (fun z => ENNReal.ofReal
          (TruncatedMoment.partition μ R V * Real.exp (V (gradient φ z)-φ z))) := by
  let ν := TruncatedMoment.target μ R V
  let : IsProbabilityMeasure ν := TruncatedMoment.probability μ hV hR
  let : ν.IsNegInvariant := TruncatedMoment.negInvariant μ hVe R
  obtain ⟨d,hd,hlow⟩ := TruncatedMoment.density_lower μ hV hR
  obtain ⟨u,hu,hmax⟩ := exists_variational_maximizer μ hR hd hlow
  let f := conjugate (Metric.ball (0:E) R) u
  have hf : NormalizedConvex R f := admissible_conjugate_normalized hR hu
  have hI := admissible_partition_integrable μ hR hd hu hlow
  have hmp := maximizer_pushforward μ (ν:=ν) hR hu hmax (TruncatedMoment.ae_mem_ball μ V R) hI
  let a := Real.log (∫ y,Real.exp (-f y) ∂μ)
  let φ := fun z => f z+a
  have hconv : ConvexOn ℝ univ φ := hf.convex.add (convexOn_const a convex_univ)
  have heven : Function.Even φ := fun z => by dsimp only [φ]; rw [hf.even z]
  have hl : LipschitzWith R φ := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [φ,dist_add_right] using hf.lipschitz.dist_le_mul z w
  have hprob : IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) := by
    rw [source_shift μ hI]
    exact normalizedSource_probability μ hI
  have hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ) := by
    intro x hx
    apply dual_add_constant_bdd _ a
    exact dual_conjugate_bdd (fun y hy => (by simpa [Metric.mem_ball,dist_zero_right] using hy : ‖y‖ < (R:ℝ)).le)
      (fun y _ => hu.nonneg y) hx
  have hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) = ν := by
    rw [source_shift μ hI,gradient_add_constant f a]
    exact hmp
  obtain ⟨c,hc,ht⟩ := admissible_tail μ hR hd hu hlow
  exact ⟨φ,hconv,heven,hl,⟨c,hc,1-a,fun z => by have hh := ht z; dsimp only [φ,f]; linarith⟩,
    hprob,hb,hm,weak_MA_of_transport μ hV hR hconv hl hb hm⟩

end CompactMomentVariational
end

open scoped InnerProductSpace ContDiff Topology
noncomputable section
namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma fenchel_eq_of_support {φ : E → ℝ} {z p : E} (hs : SupportingSlope φ z p) :
    conjugate univ φ p = ⟪z,p⟫_ℝ-φ z := by
  have hb : BddAbove ((fun w => ⟪w,p⟫_ℝ-φ w) '' univ) := by
    refine ⟨⟪z,p⟫_ℝ-φ z,?_⟩
    rintro _ ⟨w,_,rfl⟩
    have h := hs w
    rw [inner_sub_right,real_inner_comm w p,real_inner_comm z p] at h
    dsimp only
    linarith
  apply le_antisymm
  · apply conjugate_le univ_nonempty
    intro w _
    have h := hs w
    rw [inner_sub_right,real_inner_comm w p,real_inner_comm z p] at h
    linarith
  · exact le_csSup hb (mem_image_of_mem _ (mem_univ z))

lemma dual_gradient_of_support {φ : E → ℝ} {z p : E} {K : Set E} (hK : IsOpen K)
    (hp : p ∈ K) (hs : SupportingSlope φ z p)
    (hb : ∀ x ∈ K, BddAbove ((fun w => ⟪w,x⟫_ℝ-φ w) '' univ))
    (hd : DifferentiableAt ℝ (dualOn K φ) p) : gradient (dualOn K φ) p=z := by
  have he : dualOn K φ p=⟪z,p⟫_ℝ-φ z := by
    rw [dualOn_eq hp,fenchel_eq_of_support hs]
  have hm : IsLocalMin (fun y => dualOn K φ y-⟪z,y⟫_ℝ) p := by
    filter_upwards [hK.mem_nhds hp] with y hy
    have h := fenchel_dualOn hb hy z
    rw [he,real_inner_comm y z] at *
    linarith
  have hh := hm.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub (innerSL ℝ z).hasFDerivAt)
  rw [gradient,sub_eq_zero.mp hh]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply z

omit [FiniteDimensional ℝ E] in
lemma supportingSlope_of_localMin {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {z p : E}
    (hm : IsLocalMin (fun w => φ w-⟪p,w⟫_ℝ) z) : SupportingSlope φ z p := by
  have hconv : ConvexOn ℝ univ (fun w => φ w-⟪p,w⟫_ℝ) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have h := hc.2 hx hy ha hb hab
    simp only [inner_add_right,real_inner_smul_right,smul_eq_mul] at *
    nlinarith
  have hall := IsMinOn.of_isLocalMin_of_convex_univ hm hconv
  intro w
  have h := hall w
  rw [inner_sub_right]
  linarith

omit [FiniteDimensional ℝ E] in

theorem subgradient_comparison {φ q : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hφ : Continuous φ) {C : Set E} (hC : IsCompact C)
    (hboundary : ∀ y ∈ frontier C, q y ≤ φ y)
    {x p : E} (hx : x ∈ C) (hxq : φ x < q x)
    (hqs : ∀ y ∈ C, q x+⟪p,y-x⟫_ℝ ≤ q y) :
    ∃ y ∈ interior C, φ y < q y ∧ SupportingSlope φ y p := by
  obtain ⟨y,hy,hmin⟩ := hC.exists_isMinOn ⟨x,hx⟩
    ((hφ.sub (continuous_const.inner continuous_id)).continuousOn)
  have hyx : φ y-⟪p,y⟫_ℝ ≤ φ x-⟪p,x⟫_ℝ := hmin hx
  have hqy := hqs y hy
  rw [inner_sub_right] at hqy
  have hyq : φ y < q y := by linarith
  have hyint : y ∈ interior C := by
    by_contra he
    have hyfr : y ∈ frontier C := by
      rw [frontier_eq_closure_inter_closure,closure_compl]
      exact ⟨subset_closure hy,he⟩
    have hb := hboundary y hyfr
    linarith
  refine ⟨y,hyint,hyq,supportingSlope_of_localMin hc ?_⟩
  filter_upwards [isOpen_interior.mem_nhds hyint] with w hw
  exact hmin (interior_subset hw)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measure_support_image_le {μ σ ν : Measure E} [μ.IsAddHaarMeasure]
    (hν : ν ≪ μ) {φ : E → ℝ} {K D A : Set E} (hK : IsOpen K) (hcK : Convex ℝ K)
    (hb : ∀ p ∈ K, BddAbove ((fun z => ⟪z,p⟫_ℝ-φ z) '' univ))
    (hD : MeasurableSet D) (hs : ∀ᵐ p ∂ν, p ∈ K)
    (hm : Measure.map (gradient (dualOn K φ)) ν=σ)
    (hA : ∀ p ∈ A, p ∈ K → ∃ z ∈ D, SupportingSlope φ z p) :
    ν A ≤ σ D := by
  rw [← hm,Measure.map_apply (gradient_measurable _) hD]
  have hdiff : ∀ᵐ p ∂ν, p ∈ K → DifferentiableAt ℝ (dualOn K φ) p :=
    hν.ae_le (convex_ae_differentiable hK (convexOn_dualOn hcK hb))
  apply measure_mono_ae
  filter_upwards [hdiff,hs] with p hp hpk
  intro hpA
  obtain ⟨z,hz,hsz⟩ := hA p hpA hpk
  change gradient (dualOn K φ) p ∈ D
  rw [dual_gradient_of_support hK hpk hsz hb (hp hpk)]
  exact hz

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma proximal_min {φ : E → ℝ} {L : ℝ≥0} (hl : LipschitzWith L φ) (y w : E) :
    proximalEnergy φ y (proximal hl y) ≤ proximalEnergy φ y w :=
  Classical.choose_spec (proximal_exists hl y) w

omit [FiniteDimensional ℝ E] in
lemma support_of_proximal_min {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {y z : E}
    (hm : ∀ w, proximalEnergy φ y z ≤ proximalEnergy φ y w) :
    SupportingSlope φ z (y-z) := by
  intro w
  have hab (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
      0 ≤ φ w-φ z+⟪z-y,w-z⟫_ℝ+t*(‖w-z‖^2/2) := by
    have hh := hc.2 (mem_univ z) (mem_univ w) (by linarith : 0 ≤ 1-t) ht.le
      (by ring : (1-t)+t=1)
    have hmin := hm ((1-t) • z+t • w)
    have he : ‖(1-t) • z+t • w-y‖^2 = ‖z-y‖^2+2*t*⟪z-y,w-z⟫_ℝ+t^2*‖w-z‖^2 := by
      have hv : (1-t) • z+t • w-y = (z-y)+t • (w-z) := by module
      rw [hv,norm_add_sq_real,norm_smul,Real.norm_eq_abs,real_inner_smul_right]
      rw [mul_pow,sq_abs]
      ring
    dsimp only [proximalEnergy,smul_eq_mul] at hh hmin
    rw [he] at hmin
    have hm' : 0 ≤ t*(φ w-φ z+⟪z-y,w-z⟫_ℝ+t*(‖w-z‖^2/2)) := by nlinarith
    exact nonneg_of_mul_nonneg_right hm' ht
  have ht : Tendsto (fun t : ℝ => φ w-φ z+⟪z-y,w-z⟫_ℝ+t*(‖w-z‖^2/2))
      (𝓝[>] (0:ℝ)) (𝓝 (φ w-φ z+⟪z-y,w-z⟫_ℝ)) := by
    have hcont : Continuous (fun t : ℝ => φ w-φ z+⟪z-y,w-z⟫_ℝ+t*(‖w-z‖^2/2)) := by fun_prop
    simpa only [zero_mul,add_zero] using (hcont.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hn : 0 ≤ φ w-φ z+⟪z-y,w-z⟫_ℝ := ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact hab t ht ht1)
  have he : y-z=-(z-y) := by module
  rw [he,inner_neg_left]
  linarith

lemma proximal_support {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (y : E) : SupportingSlope φ (proximal hl y) (y-proximal hl y) :=
  support_of_proximal_min hc (proximal_min hl y)

omit [FiniteDimensional ℝ E] in
lemma supporting_monotone {φ : E → ℝ} {z w p q : E}
    (hsz : SupportingSlope φ z p) (hsw : SupportingSlope φ w q) :
    0 ≤ ⟪p-q,z-w⟫_ℝ := by
  have hz := hsz w
  have hw := hsw z
  simp only [inner_sub_left,inner_sub_right] at *
  linarith

omit [FiniteDimensional ℝ E] in
lemma proximal_firm_of_support {φ : E → ℝ} {z w y x : E}
    (hz : SupportingSlope φ z (y-z)) (hw : SupportingSlope φ w (x-w)) :
    ‖z-w‖^2 ≤ ⟪y-x,z-w⟫_ℝ := by
  have ht := supporting_monotone hz hw
  have he : (y-z)-(x-w)=(y-x)-(z-w) := by module
  rw [he,inner_sub_left,real_inner_self_eq_norm_sq] at ht
  linarith

lemma proximal_firm {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (y x : E) :
    ‖proximal hl y-proximal hl x‖^2 ≤ ⟪y-x,proximal hl y-proximal hl x⟫_ℝ :=
  proximal_firm_of_support (proximal_support hc hl y) (proximal_support hc hl x)

lemma proximal_lipschitz {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) : LipschitzWith 1 (proximal hl) := by
  apply LipschitzWith.of_dist_le_mul
  intro y x
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  have h := (proximal_firm hc hl y x).trans (real_inner_le_norm _ _)
  by_cases hn : ‖proximal hl y-proximal hl x‖=0
  · rw [hn]; exact norm_nonneg _
  · have hp : 0 < ‖proximal hl y-proximal hl x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    nlinarith

lemma proximal_eq_of_support {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) {y z : E} (hz : SupportingSlope φ z (y-z)) : proximal hl y=z := by
  have h := proximal_firm_of_support (proximal_support hc hl y) hz
  simp only [sub_self,inner_zero_left] at h
  have hn : ‖proximal hl y-z‖=0 := by nlinarith [norm_nonneg (proximal hl y-z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma proximal_add_slope {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) {z p : E} (hz : SupportingSlope φ z p) : proximal hl (z+p)=z := by
  apply proximal_eq_of_support hc hl
  simpa only [add_sub_cancel_left] using hz

lemma gradient_eq_of_support {φ : E → ℝ} {x p : E}
    (hd : DifferentiableAt ℝ φ x) (hs : SupportingSlope φ x p) : gradient φ x=p := by
  have hm : IsLocalMin (fun z => φ z-⟪p,z⟫_ℝ) x := by
    apply Eventually.of_forall
    intro z
    have h := hs z
    rw [inner_sub_right] at h
    linarith
  have he := hm.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt)
  rw [gradient,sub_eq_zero.mp he]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply p

end CompactMomentVariational
end
open scoped ENNReal
noncomputable section
namespace ConvexRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma lipschitz_image_null {L : ℝ≥0} {f : E → E} (hl : LipschitzWith L f)
    {s : Set E} (hs : μ s=0) : μ (f '' s)=0 := by
  have ha : μ ≪ μH[Module.finrank ℝ E] := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hb : μH[Module.finrank ℝ E] ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply ha
  apply le_antisymm _ (zero_le)
  simpa only [hb hs,mul_zero] using hl.hausdorffMeasure_image_le
    (d:=(Module.finrank ℝ E : ℝ)) (by positivity) s

lemma ae_regular_preimage {L : ℝ≥0} {f : E → E} (hl : LipschitzWith L f) :
    ∀ᵐ x ∂μ, ∀ y, f y=x → DifferentiableAt ℝ f y ∧ (fderiv ℝ f y).det ≠ 0 := by
  let A := {y | ¬ DifferentiableAt ℝ f y}
  let B := {y | DifferentiableAt ℝ f y ∧ (fderiv ℝ f y).det=0}
  have hA : μ (f '' A)=0 := lipschitz_image_null μ hl
    (ae_iff.mp (hl.ae_differentiableAt (μ:=μ)))
  have hB : μ (f '' B)=0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun y hy => hy.1.hasFDerivAt.hasFDerivWithinAt) (fun _ hy => hy.2)
  have ha : ∀ᵐ x ∂μ, x ∉ f '' A := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hA
  have hb : ∀ᵐ x ∂μ, x ∉ f '' B := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ha,hb] with x hxA hxB
  intro y hy
  have hd : DifferentiableAt ℝ f y := by
    by_contra he
    exact hxA ⟨y,he,hy⟩
  refine ⟨hd,?_⟩
  intro he
  exact hxB ⟨y,⟨hd,he⟩,hy⟩

end ConvexRegularity
namespace CompactMomentVariational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma norm_chosenSlope_le {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (x : E) : ‖chosenSlope μ hc hl x‖ ≤ (L:ℝ) :=
  (Classical.choose_spec (exists_supportingSlope μ hc hl x)).1

lemma chosenSlope_support {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (x : E) : SupportingSlope φ x (chosenSlope μ hc hl x) :=
  (Classical.choose_spec (exists_supportingSlope μ hc hl x)).2

lemma chosenSlope_eq_gradient {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) {x : E} (hd : DifferentiableAt ℝ φ x) :
    chosenSlope μ hc hl x=gradient φ x :=
  (gradient_eq_of_support hd (chosenSlope_support μ hc hl x)).symm

lemma chosenSlope_continuousAt {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) {x : E} (hd : DifferentiableAt ℝ φ x) :
    ContinuousAt (chosenSlope μ hc hl) x := by
  apply (isCompact_closedBall (0:E) (L:ℝ)).tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall fun y => by
      simpa only [Metric.mem_closedBall,dist_zero_right] using norm_chosenSlope_le μ hc hl y
  · intro p _ hp
    let P := chosenSlope μ hc hl
    let F := Filter.comap P (𝓝 p) ⊓ 𝓝 x
    have : F.NeBot := neBot_inf_comap_iff_map'.mpr hp
    have hs : SupportingSlope φ x p := supportingSlope_limit hl.continuous
      (show Tendsto (id : E → E) F (𝓝 x) from inf_le_right)
      (show Tendsto P F (𝓝 p) from map_le_iff_le_comap.mpr inf_le_left)
      (Eventually.of_forall (chosenSlope_support μ hc hl))
    exact (gradient_eq_of_support hd hs).symm.trans (chosenSlope_eq_gradient μ hc hl hd).symm

theorem ae_chosenSlope_differentiable {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    {L : ℝ≥0} (hl : LipschitzWith L φ) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x ∧ DifferentiableAt ℝ (chosenSlope μ hc hl) x := by
  have hr := ConvexRegularity.ae_regular_preimage μ (proximal_lipschitz hc hl)
  filter_upwards [hr,hl.ae_differentiableAt (μ:=μ)] with x hx hd
  refine ⟨hd,?_⟩
  let P := chosenSlope μ hc hl
  let T := fun y : E => y+P y
  have hleft (y : E) : proximal hl (T y)=y := proximal_add_slope hc hl (chosenSlope_support μ hc hl y)
  obtain ⟨hp,hdet⟩ := hx (T x) (hleft x)
  let e : E ≃L[ℝ] E := ((fderiv ℝ (proximal hl) (T x)).toLinearMap.equivOfDetNeZero hdet).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E)=fderiv ℝ (proximal hl) (T x) := rfl
  have ht : ContinuousAt T x := continuousAt_id.add (chosenSlope_continuousAt μ hc hl hd)
  have hprox : HasFDerivAt (proximal hl) (e : E →L[ℝ] E) (T x) := by rw [he]; exact hp.hasFDerivAt
  have hi : HasFDerivAt T (e.symm : E →L[ℝ] E) x :=
    hprox.of_local_left_inverse ht (Eventually.of_forall hleft)
  have hg := hi.sub (hasFDerivAt_id x)
  have hh : T-id=P := by funext y; exact add_sub_cancel_left y (P y)
  rw [hh] at hg
  exact hg.differentiableAt

lemma ae_gradient_hasFDerivWithin {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    {L : ℝ≥0} (hl : LipschitzWith L φ) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x ∧
      HasFDerivWithinAt (gradient φ) (fderiv ℝ (chosenSlope μ hc hl) x)
        {y | DifferentiableAt ℝ φ y} x := by
  filter_upwards [ae_chosenSlope_differentiable μ hc hl] with x hx
  exact ⟨hx.1,hx.2.hasFDerivAt.hasFDerivWithinAt.congr'
    (fun _ hy => (chosenSlope_eq_gradient μ hc hl hy).symm) hx.1⟩

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace MomentJacobian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem jacobian_of_ae_inverse_within {σ ν : Measure E} {K D : Set E}
    (_hK : MeasurableSet K) {g f : E → E} {g' : E → E →L[ℝ] E}
    (hgm : Measurable g) (hf : Measurable f)
    (hg : ∀ᵐ z ∂μ, z ∈ D ∧ HasFDerivWithinAt g (g' z) D z)
    (hm : Measure.map g σ = ν) (hμσ : μ ≪ σ) (hσμ : σ ≪ μ)
    (hKν : μ.restrict K ≪ ν)
    (hi : ∀ᵐ z ∂σ, f (g z)=z) (hk : ∀ᵐ z ∂σ, g z ∈ K) :
    μ.withDensity (fun z => ENNReal.ofReal |(g' z).det|) = Measure.map f (μ.restrict K) := by
  let s := {z | z ∈ D ∧ HasFDerivWithinAt g (g' z) D z ∧ f (g z)=z ∧ g z ∈ K}
  have hfull : ∀ᵐ z ∂μ, z ∈ s := by
    filter_upwards [hg,hμσ.ae_le hi,hμσ.ae_le hk] with z hz hi hk
    exact ⟨hz.1,hz.2,hi,hk⟩
  have hsn : NullMeasurableSet s μ := by
    apply NullMeasurableSet.of_compl
    exact NullMeasurableSet.of_null (ae_iff.mp hfull)
  obtain ⟨t,hts,ht,heq⟩ := hsn.exists_measurable_subset_ae_eq
  have htfull : ∀ᵐ z ∂μ, z ∈ t := by
    filter_upwards [hfull,heq] with z hz he
    exact he.mpr hz
  have hsinj : InjOn g t := by
    intro z hz w hw he
    exact (hts hz).2.2.1.symm.trans ((congrArg f he).trans (hts hw).2.2.1)
  have hder (z) (hz : z ∈ t) : HasFDerivWithinAt g (g' z) t z :=
    ((hts hz).2.1).mono (fun w hw => (hts hw).1)
  have him : MeasurableSet (g '' t) := measurable_image_of_fderivWithin ht hder hsinj
  have htfullσ : ∀ᵐ z ∂σ, z ∈ t := hσμ.ae_le htfull
  have himfullν : ∀ᵐ x ∂ν, x ∈ g '' t := by
    rw [← hm]
    exact (ae_map_iff hgm.aemeasurable him).mpr
      (htfullσ.mono (fun z hz => mem_image_of_mem g hz))
  have himless : g '' t ⊆ K := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hts hz).2.2.2
  have himrestrict : μ.restrict (g '' t)=μ.restrict K := by
    rw [← Measure.restrict_eq_self_of_ae_mem (hKν.ae_le himfullν),
      Measure.restrict_restrict him,inter_eq_left.mpr himless]
  have hj := map_withDensity_abs_det_fderiv_eq_addHaar μ ht.nullMeasurableSet hder hsinj
  rw [Measure.restrict_eq_self_of_ae_mem htfull,himrestrict] at hj
  rw [← hj,Measure.map_map hf hgm]
  have hie : ∀ᵐ z ∂μ.withDensity (fun z => ENNReal.ofReal |(g' z).det|), f (g z)=z :=
    (withDensity_absolutelyContinuous _ _).ae_le (hμσ.ae_le hi)
  exact ((Measure.map_congr hie).trans Measure.map_id).symm

end MomentJacobian
namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem ae_abs_det_of_weak_truncated {V φ : E → ℝ} (hV : Continuous V)
    {R : ℝ≥0} (hR : 0 < R) (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      TruncatedMoment.target μ R V) :
    ∀ᵐ z ∂μ, |(fderiv ℝ (chosenSlope μ hc hl) z).det| =
      TruncatedMoment.partition μ R V * Real.exp (V (gradient φ z)-φ z) := by
  let σ := μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))
  let ν := TruncatedMoment.target μ R V
  let K := Metric.ball (0:E) (R:ℝ)
  let Z := TruncatedMoment.partition μ R V
  have hZ : 0 < Z := TruncatedMoment.partition_pos μ hV hR
  have hμσ : μ ≪ σ := withDensity_absolutelyContinuous'
    hl.continuous.neg.rexp.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall (fun _ => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
  have hσμ : σ ≪ μ := withDensity_absolutelyContinuous _ _
  have hνμ : ν ≪ μ := (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hKν : μ.restrict K ≪ ν := withDensity_absolutelyContinuous'
    (hV.neg.rexp.measurable.div_const Z).ennreal_ofReal.aemeasurable
    (Eventually.of_forall (fun _ => ENNReal.ofReal_ne_zero_iff.mpr (div_pos (Real.exp_pos _) hZ)))
  have hinv := weak_inverse hσμ hνμ Metric.isOpen_ball (convex_ball (0:E) R) hc hl hb
    (TruncatedMoment.ae_mem_ball μ V R) hm
  have hs : ∀ᵐ z ∂σ, gradient φ z ∈ K := by
    have ht := TruncatedMoment.ae_mem_ball μ V R
    rw [← hm] at ht
    exact ae_of_ae_map (gradient_measurable _).aemeasurable ht
  have hdet := MomentJacobian.jacobian_of_ae_inverse_within μ Metric.isOpen_ball.measurableSet
    (gradient_measurable _) (gradient_measurable _) (ae_gradient_hasFDerivWithin μ hc hl)
    hm hμσ hσμ hKν hinv hs
  have he := hdet.trans (weak_MA_of_transport μ hV hR hc hl hb hm)
  have hJm : Measurable (fun z => |(fderiv ℝ (chosenSlope μ hc hl) z).det|) :=
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ _)).abs
  have hWm : Measurable (fun z => Z * Real.exp (V (gradient φ z)-φ z)) :=
    measurable_const.mul ((hV.measurable.comp (gradient_measurable _)).sub hl.continuous.measurable).exp
  have hae := (withDensity_eq_iff_of_sigmaFinite hJm.ennreal_ofReal.aemeasurable
    hWm.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hae] with z hz
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (mul_pos hZ (Real.exp_pos _)).le).mp hz

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma proximalConjugate_support {φ : E → ℝ} {L : ℝ≥0}
    (hl : LipschitzWith L φ) (y : E) :
    SupportingSlope (proximalConjugate hl) y (proximal hl y) := by
  intro w
  have hh := proximal_min hl w (proximal hl y)
  dsimp only [proximalEnergy] at hh
  rw [norm_sub_sq_real,norm_sub_sq_real] at hh
  dsimp only [proximalConjugate]
  rw [inner_sub_right]
  linarith

lemma proximalConjugate_remainder {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (y w : E) :
    |proximalConjugate hl w-proximalConjugate hl y-⟪proximal hl y,w-y⟫_ℝ| ≤ ‖w-y‖^2 := by
  have hlow := proximalConjugate_support hl y w
  have hupp := proximalConjugate_support hl w y
  have hi := real_inner_le_norm (proximal hl w-proximal hl y) (w-y)
  have hp := (proximal_lipschitz hc hl).dist_le_mul w y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm] at hp
  rw [abs_of_nonneg (by linarith)]
  have hbound := mul_le_mul_of_nonneg_right hp (norm_nonneg (w-y))
  simp only [inner_sub_left,inner_sub_right] at hupp hi ⊢
  nlinarith

lemma proximalConjugate_hasFDerivAt {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (y : E) :
    HasFDerivAt (proximalConjugate hl) (innerSL ℝ (proximal hl y)) y := by
  rw [hasFDerivAt_iff_isLittleO]
  apply (Asymptotics.isBigO_of_le (𝓝 y) (fun w => ?_)).trans_isLittleO
    (Asymptotics.isLittleO_pow_sub_sub y (by norm_num : 1 < (2:ℕ)))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖w-y‖),innerSL_apply_apply] using
    proximalConjugate_remainder hc hl y w

lemma proximal_derivative_symmetric {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) {y : E} {H : E →L[ℝ] E} (hH : HasFDerivAt (proximal hl) H y)
    (v w : E) : ⟪H v,w⟫_ℝ=⟪v,H w⟫_ℝ := by
  have hd := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.hasFDerivAt.comp y hH
  have hh := second_derivative_symmetric (proximalConjugate_hasFDerivAt hc hl) hd v w
  change ⟪H v,w⟫_ℝ=⟪H w,v⟫_ℝ at hh
  exact hh.trans (real_inner_comm _ _)

omit [FiniteDimensional ℝ E] in
lemma supporting_selection_monotone_line {φ : E → ℝ} {P : E → E}
    (hs : ∀ x, SupportingSlope φ x (P x)) (x v : E) :
    Monotone (fun t : ℝ => ⟪P (x+t • v),v⟫_ℝ) := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  have hm := supporting_monotone (hs (x+b • v)) (hs (x+a • v))
  have he : (x+b • v)-(x+a • v)=(b-a) • v := by module
  rw [he,real_inner_smul_right] at hm
  have hi := nonneg_of_mul_nonneg_right hm (sub_pos.mpr hab)
  simpa only [inner_sub_left,sub_nonneg] using hi

omit [FiniteDimensional ℝ E] in
lemma supporting_derivative_nonneg {φ : E → ℝ} {P : E → E}
    (hs : ∀ x, SupportingSlope φ x (P x)) {x : E} {H : E →L[ℝ] E}
    (hH : HasFDerivAt P H x) (v : E) : 0 ≤ ⟪H v,v⟫_ℝ := by
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [one_smul,id_eq] using
      ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hP : HasDerivAt (fun t : ℝ => P (x+t • v)) (H v) 0 := by
    have hh : HasFDerivAt P H (x+(0:ℝ) • v) := by simpa only [zero_smul,add_zero] using hH
    exact hh.comp_hasDerivAt (0:ℝ) hline
  have hh := hP.inner ℝ (hasDerivAt_const (0:ℝ) v)
  simp only [inner_zero_right,zero_add] at hh
  have hm := (supporting_selection_monotone_line hs x v).deriv_nonneg (x:=0)
  rwa [hh.deriv] at hm

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem ae_chosenSlope_positive {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    {L : ℝ≥0} (hl : LipschitzWith L φ) :
    ∀ᵐ x ∂μ, (fderiv ℝ (chosenSlope μ hc hl) x).toLinearMap.IsPositive := by
  have hr := ConvexRegularity.ae_regular_preimage μ (proximal_lipschitz hc hl)
  filter_upwards [hr,hl.ae_differentiableAt (μ:=μ)] with x hx hd
  let P := chosenSlope μ hc hl
  let T := fun y : E => y+P y
  have hleft (y : E) : proximal hl (T y)=y := proximal_add_slope hc hl (chosenSlope_support μ hc hl y)
  obtain ⟨hp,hdet⟩ := hx (T x) (hleft x)
  let e : E ≃L[ℝ] E := ((fderiv ℝ (proximal hl) (T x)).toLinearMap.equivOfDetNeZero hdet).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E)=fderiv ℝ (proximal hl) (T x) := rfl
  have ht : ContinuousAt T x := continuousAt_id.add (chosenSlope_continuousAt μ hc hl hd)
  have hprox : HasFDerivAt (proximal hl) (e : E →L[ℝ] E) (T x) := by rw [he]; exact hp.hasFDerivAt
  have hi : HasFDerivAt T (e.symm : E →L[ℝ] E) x :=
    hprox.of_local_left_inverse ht (Eventually.of_forall hleft)
  have hg := hi.sub (hasFDerivAt_id x)
  have hh : T-id=P := by funext y; exact add_sub_cancel_left y (P y)
  rw [hh] at hg
  have hsymm (v w : E) : ⟪e v,w⟫_ℝ=⟪v,e w⟫_ℝ :=
    proximal_derivative_symmetric hc hl hprox v w
  have hsi (v w : E) : ⟪e.symm v,w⟫_ℝ=⟪v,e.symm w⟫_ℝ := by
    have h := hsymm (e.symm v) (e.symm w)
    simpa only [e.apply_symm_apply] using h.symm
  rw [hg.fderiv]
  refine ⟨?_,?_⟩
  · intro v w
    change ⟪e.symm v-v,w⟫_ℝ=⟪v,e.symm w-w⟫_ℝ
    rw [inner_sub_left,inner_sub_right,hsi]
  · intro v
    change 0 ≤ ⟪((e.symm : E →L[ℝ] E)-ContinuousLinearMap.id ℝ E) v,v⟫_ℝ
    exact supporting_derivative_nonneg (chosenSlope_support μ hc hl) hg v

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_weakHessian (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ}
    (hc : ConvexOn ℝ univ φ) {L : ℝ≥0} (hl : LipschitzWith L φ) (z : E) :
    (weakHessian μ b hc hl z).det = (fderiv ℝ (chosenSlope μ hc hl) z).det :=
  LinearMap.det_toMatrix b.toBasis _

theorem ae_positive_MA (b : OrthonormalBasis ι ℝ E) {V φ : E → ℝ} (hV : Continuous V)
    {R : ℝ≥0} (hR : 0 < R) (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      TruncatedMoment.target μ R V) :
    ∀ᵐ z ∂μ, DifferentiableAt ℝ φ z ∧ DifferentiableAt ℝ (chosenSlope μ hc hl) z ∧
      (weakHessian μ b hc hl z).PosDef ∧
      Real.log (weakHessian μ b hc hl z).det =
        V (chosenSlope μ hc hl z)+Real.log (TruncatedMoment.partition μ R V)-φ z ∧
      chosenSlope μ hc hl z ∈ Metric.ball (0:E) R := by
  have hZ : 0 < TruncatedMoment.partition μ (R:ℝ) V := TruncatedMoment.partition_pos μ hV hR
  have hμσ := withDensity_absolutelyContinuous' (μ := μ)
    hl.continuous.neg.rexp.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall (fun _ : E => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
  have ht := TruncatedMoment.ae_mem_ball μ V R
  rw [← hm] at ht
  have hmem := hμσ.ae_le (ae_of_ae_map (gradient_measurable _).aemeasurable ht)
  filter_upwards [ae_chosenSlope_differentiable μ hc hl,ae_chosenSlope_positive μ hc hl,
    ae_abs_det_of_weak_truncated μ hV hR hc hl hb hm,hmem] with z hz hp hj hball
  have hps : (weakHessian μ b hc hl z).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).mpr hp
  rw [← det_weakHessian μ b hc hl z,abs_of_nonneg hps.det_nonneg] at hj
  have hd : (weakHessian μ b hc hl z).PosDef := hps.posDef_iff_det_ne_zero.mpr (by
    rw [hj]; exact (mul_pos hZ (Real.exp_pos _)).ne')
  refine ⟨hz.1,hz.2,hd,?_,?_⟩
  · rw [chosenSlope_eq_gradient μ hc hl hz.1]
    calc
      Real.log (weakHessian μ b hc hl z).det =
          Real.log (TruncatedMoment.partition μ (R:ℝ) V * Real.exp (V (gradient φ z)-φ z)) :=
        congrArg Real.log hj
      _ = Real.log (TruncatedMoment.partition μ (R:ℝ) V)+Real.log (Real.exp (V (gradient φ z)-φ z)) :=
        Real.log_mul hZ.ne' (Real.exp_ne_zero _)
      _ = _ := by rw [Real.log_exp]; ring
  · rwa [chosenSlope_eq_gradient μ hc hl hz.1]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma supporting_selection_injective_at {q : E → ℝ} {P : E → E}
    (hs : ∀ x, SupportingSlope q x (P x)) {x y : E} {H : E →L[ℝ] E}
    (hH : HasFDerivAt P H x) (hpos : ∀ v ≠ 0, 0 < ⟪H v,v⟫_ℝ)
    (he : P x=P y) : x=y := by
  by_contra hne
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let g := fun t : ℝ => ⟪P (x+t • v),v⟫_ℝ
  have hg : Monotone g := supporting_selection_monotone_line hs x v
  have h01 : g 0=g 1 := by
    have hxy : x+(y-x)=y := by abel
    simp only [g,zero_smul,add_zero,one_smul,v,hxy,he]
  have hconst : ∀ t ∈ Icc (0:ℝ) 1, g t=g 0 := by
    intro t ht
    apply le_antisymm
    · exact (hg ht.2).trans_eq h01.symm
    · exact hg ht.1
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hP : HasDerivAt (fun t : ℝ => P (x+t • v)) (H v) 0 := by
    have hh : HasFDerivAt P H (x+(0:ℝ) • v) := by simpa only [zero_smul,add_zero] using hH
    exact hh.comp_hasDerivAt (0:ℝ) hline
  have hd : HasDerivAt g ⟪H v,v⟫_ℝ 0 := by
    simpa only [inner_zero_right,zero_add] using hP.inner ℝ (hasDerivAt_const (0:ℝ) v)
  have hc : HasDerivWithinAt g 0 (Icc (0:ℝ) 1) 0 := by
    apply (hasDerivWithinAt_const (0:ℝ) (Icc (0:ℝ) 1) (g 0)).congr
    · exact hconst
    · rfl
  have hzero := UniqueDiffWithinAt.eq_deriv (Icc (0:ℝ) 1)
    (uniqueDiffOn_Icc_zero_one 0 (by simp)) hd.hasDerivWithinAt hc
  exact (hpos v hv).ne' hzero

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem ae_weighted_jacobian_comparison {σ : Measure E} {w : E → ℝ≥0∞}
    {φ q : E → ℝ} {P : E → E} {K C : Set E} (hK : IsOpen K) (hcK : Convex ℝ K)
    (hb : ∀ p ∈ K, BddAbove ((fun z => ⟪z,p⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient (dualOn K φ)) ((μ.restrict K).withDensity w)=σ)
    (hc : ConvexOn ℝ univ φ) (hφ : Continuous φ) (hq : Continuous q)
    (hP : ∀ x, SupportingSlope q x (P x)) (hC : IsCompact C)
    (hboundary : ∀ y ∈ frontier C, q y ≤ φ y)
    (hreg : ∀ᵐ x ∂μ, DifferentiableAt ℝ q x ∧ DifferentiableAt ℝ P x ∧
      (∀ v ≠ 0, 0 < ⟪(fderiv ℝ P x) v,v⟫_ℝ) ∧ P x ∈ K) :
    (∫⁻ x in {x | x ∈ interior C ∧ φ x < q x},
      ENNReal.ofReal |(fderiv ℝ P x).det| * w (gradient q x) ∂μ) ≤
      σ {x | x ∈ interior C ∧ φ x < q x} := by
  let D := {x | x ∈ interior C ∧ φ x < q x}
  have hD : MeasurableSet D := (isOpen_interior.inter (isOpen_lt hφ hq)).measurableSet
  let A := {x | DifferentiableAt ℝ q x ∧ DifferentiableAt ℝ P x ∧
      (∀ v ≠ 0, 0 < ⟪(fderiv ℝ P x) v,v⟫_ℝ) ∧ P x ∈ K}
  have hAn : NullMeasurableSet A μ := NullMeasurableSet.of_compl
    (NullMeasurableSet.of_null (ae_iff.mp hreg))
  obtain ⟨T,hTA,hT,hTeq⟩ := hAn.exists_measurable_subset_ae_eq
  have hTfull : ∀ᵐ x ∂μ, x ∈ T := by
    filter_upwards [hreg,hTeq] with x hx he
    exact he.mpr hx
  let S := T ∩ D
  have hS : MeasurableSet S := hT.inter hD
  have hSeq : S =ᵐ[μ] D := by
    filter_upwards [hTfull] with x hx
    exact propext (and_iff_right hx)
  have hder (x) (hx : x ∈ S) : HasFDerivWithinAt (gradient q) (fderiv ℝ P x) S x := by
    apply (hTA hx.1).2.1.hasFDerivAt.hasFDerivWithinAt.congr'
    · intro y hy
      exact gradient_eq_of_support (hTA hy.1).1 (hP y)
    · exact hx
  have hinj : InjOn (gradient q) S := by
    intro x hx y hy he
    apply supporting_selection_injective_at hP (hTA hx.1).2.1.hasFDerivAt (hTA hx.1).2.2.1
    rwa [gradient_eq_of_support (hTA hx.1).1 (hP x),
      gradient_eq_of_support (hTA hy.1).1 (hP y)] at he
  have hA : MeasurableSet ((gradient q) '' S) := measurable_image_of_fderivWithin hS hder hinj
  have him : (gradient q) '' S ⊆ K := by
    rintro _ ⟨x,hx,rfl⟩
    rw [gradient_eq_of_support (hTA hx.1).1 (hP x)]
    exact (hTA hx.1).2.2.2
  have hνμ : ((μ.restrict K).withDensity w) ≪ μ :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hs : ∀ᵐ p ∂(μ.restrict K).withDensity w, p ∈ K :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hK.measurableSet)
  have ht : ((μ.restrict K).withDensity w) ((gradient q) '' S) ≤ σ D := by
    apply measure_support_image_le hνμ hK hcK hb hD hs hm
    rintro p ⟨x,hx,rfl⟩ _
    have hps : SupportingSlope q x (gradient q x) := by
      rw [gradient_eq_of_support (hTA hx.1).1 (hP x)]
      exact hP x
    obtain ⟨y,hy,hyq,hys⟩ := subgradient_comparison hc hφ hC hboundary
      (interior_subset hx.2.1) hx.2.2 (fun y _ => hps y)
    exact ⟨y,⟨hy,hyq⟩,hys⟩
  rw [withDensity_apply w hA,Measure.restrict_restrict hA,inter_eq_left.mpr him,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hS hder hinj w,
    Measure.restrict_congr_set hSeq] at ht
  exact ht

theorem ae_strict_weighted_comparison {r w : E → ℝ≥0∞}
    {φ q : E → ℝ} {P : E → E} {K C : Set E} (hK : IsOpen K) (hcK : Convex ℝ K)
    (hb : ∀ p ∈ K, BddAbove ((fun z => ⟪z,p⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient (dualOn K φ)) ((μ.restrict K).withDensity w)=μ.withDensity r)
    (hc : ConvexOn ℝ univ φ) (hφ : Continuous φ) (hq : Continuous q)
    (hP : ∀ x, SupportingSlope q x (P x)) (hC : IsCompact C)
    (hboundary : ∀ y ∈ frontier C, q y ≤ φ y)
    (hreg : ∀ᵐ x ∂μ, DifferentiableAt ℝ q x ∧ DifferentiableAt ℝ P x ∧
      (∀ v ≠ 0, 0 < ⟪(fderiv ℝ P x) v,v⟫_ℝ) ∧ P x ∈ K)
    (hfinite : (μ.withDensity r) C ≠ ⊤) (hw : Measurable w)
    (hstrict : ∀ᵐ x ∂μ, x ∈ interior C → φ x < q x →
      r x < ENNReal.ofReal |(fderiv ℝ P x).det| * w (gradient q x)) :
    ∀ x ∈ C, q x ≤ φ x := by
  intro x hx
  by_contra he
  have hxq : φ x < q x := lt_of_not_ge he
  have hxint : x ∈ interior C := by
    by_contra hh
    have hxf : x ∈ frontier C := by
      rw [frontier_eq_closure_inter_closure,closure_compl]
      exact ⟨subset_closure hx,hh⟩
    exact (hboundary x hxf).not_gt hxq
  let D := {x | x ∈ interior C ∧ φ x < q x}
  have hDo : IsOpen D := isOpen_interior.inter (isOpen_lt hφ hq)
  have hDμ : μ D ≠ 0 := ne_of_gt (hDo.measure_pos μ ⟨x,hxint,hxq⟩)
  have hDsub : D ⊆ C := fun _ hz => interior_subset hz.1
  have hDf : (∫⁻ z in D, r z ∂μ) ≠ ⊤ := by
    rw [← withDensity_apply r hDo.measurableSet]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hDsub) (lt_top_iff_ne_top.mpr hfinite))
  have hJ : Measurable (fun x => ENNReal.ofReal |(fderiv ℝ P x).det| * w (gradient q x)) :=
    ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ P)).abs.ennreal_ofReal).mul
      (hw.comp (gradient_measurable q))
  have hlt := setLIntegral_strict_mono hDo.measurableSet hDμ hJ hDf
    (hstrict.mono (fun z hz hzD => hz hzD.1 hzD.2))
  have hle := ae_weighted_jacobian_comparison μ hK hcK hb hm hc hφ hq hP hC hboundary hreg
  rw [withDensity_apply r hDo.measurableSet] at hle
  exact (not_lt_of_ge hle) hlt

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma radial_lower_of_finite_dual {φ : E → ℝ} {R a : ℝ}
    (ha : 0 < a) (haR : a < R)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ z, a*‖z‖-b ≤ φ z := by
  let u := dualOn (Metric.ball (0:E) R) φ
  have hsub : Metric.closedBall (0:E) a ⊆ Metric.ball (0:E) R :=
    Metric.closedBall_subset_ball haR
  have hu : ContinuousOn u (Metric.closedBall (0:E) a) :=
    ((convexOn_dualOn (convex_ball (0:E) R) hb).continuousOn Metric.isOpen_ball).mono hsub
  obtain ⟨x,hx,hmax⟩ := (isCompact_closedBall (0:E) a).exists_isMaxOn
    ⟨0,Metric.mem_closedBall_self ha.le⟩ hu
  let b := max (u x) 0
  refine ⟨b,le_max_right _ _,?_⟩
  intro z
  by_cases hz : z=0
  · subst z
    have hf := fenchel_dualOn hb (hsub (Metric.mem_closedBall_self ha.le)) (0:E)
    have hle : u 0 ≤ b := (hmax (Metric.mem_closedBall_self ha.le)).trans (le_max_left _ _)
    simp only [inner_zero_right,norm_zero,mul_zero,zero_sub] at *
    linarith
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let y := (a/‖z‖) • z
    have hyn : ‖y‖=a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ha hn),div_mul_cancel₀ _ hn.ne']
    have hy : y ∈ Metric.closedBall (0:E) a := by
      rw [Metric.mem_closedBall,dist_zero_right,hyn]
    have hf := fenchel_dualOn hb (hsub hy) z
    have hle : u y ≤ b := (hmax hy).trans (le_max_left _ _)
    have hi : ⟪y,z⟫_ℝ=a*‖z‖ := by
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    rw [hi] at hf
    change a*‖z‖-u y ≤ φ z at hf
    linarith

end CompactMomentVariational

namespace WeakMomentBound
open CompactMomentVariational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma ball_alignment {u v : E} {R d : ℝ} (hu : ‖u‖ = 1)
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (halign : R-d ≤ ⟪v,u⟫_ℝ) :
    ‖v - R • u‖^2 ≤ 2*R*d := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hR, hu, mul_one]
  have hsq : ‖v‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma difference_alignment {u v w : E} {R d : ℝ} (hu : ‖u‖ = 1)
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hav : R-d ≤ ⟪v,u⟫_ℝ) (haw : R-d ≤ ⟪w,u⟫_ℝ) :
    ‖v-w‖^2 ≤ 8*R*d := by
  have hv' := ball_alignment hu hR hv hav
  have hw' := ball_alignment hu hR hw haw
  have htri : ‖v-w‖ ≤ ‖v-R • u‖ + ‖w-R • u‖ := by
    have := norm_sub_le (v-R • u) (w-R • u)
    simpa only [sub_sub_sub_cancel_right, norm_sub_rev] using this
  have hsq := pow_le_pow_left₀ (norm_nonneg (v-w)) htri 2
  nlinarith [sq_nonneg (‖v-R • u‖-‖w-R • u‖)]

omit [FiniteDimensional ℝ E] in
lemma secondDiff_nonneg {φ : E → ℝ} {G : E → E}
    (hG : ∀ x, SupportingSlope φ x (G x)) (h z : E) :
    0 ≤ secondDiff φ h z := by
  have hp := hG z (z+h)
  have hm := hG z (z-h)
  simp only [add_sub_cancel_left, sub_sub_cancel_left, inner_neg_right] at hp hm
  dsimp [secondDiff]
  linarith

omit [FiniteDimensional ℝ E] in
lemma secondDiff_le_gradient {φ : E → ℝ} {G : E → E}
    (hG : ∀ x, SupportingSlope φ x (G x)) (h z : E) :
    secondDiff φ h z ≤ ‖G (z+h)-G (z-h)‖ * ‖h‖ := by
  have hp := hG (z+h) z
  have hm := hG (z-h) z
  simp only [sub_add_cancel_left, sub_sub_cancel, inner_neg_right] at hp hm
  have hi := real_inner_le_norm (G (z+h)-G (z-h)) h
  rw [inner_sub_left] at hi
  dsimp [secondDiff]
  linarith

omit [FiniteDimensional ℝ E] in
lemma slope_alignment {φ : E → ℝ} {G : E → E} {R a b η : ℝ}
    (hG : ∀ x, SupportingSlope φ x (G x))
    (hbound : ∀ x, ‖G x‖ ≤ R) (ha : 0 ≤ a) (hlower : ∀ x, a*‖x‖-b ≤ φ x)
    {z k : E} (hz : 0 < ‖z‖)
    (hlarge : b + |φ 0| + (a+R)*‖k‖ ≤ η*‖z‖) :
    a-η ≤ ⟪G (z+k), ‖z‖⁻¹ • z⟫_ℝ := by
  have hs := hG (z+k) 0
  simp only [zero_sub, inner_neg_right, inner_add_right] at hs
  have hn : ‖z‖ ≤ ‖z+k‖+‖k‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (z+k) k
  have hi : ⟪G (z+k),k⟫_ℝ ≤ R*‖k‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _))
  have hl := hlower (z+k)
  have hn' := mul_le_mul_of_nonneg_left hn ha
  have hi' : (a-η)*‖z‖ ≤ ⟪G (z+k),z⟫_ℝ := by
    have habs := le_abs_self (φ (0:E))
    nlinarith
  rw [real_inner_smul_right]
  apply (le_inv_mul_iff₀ hz).mpr
  nlinarith

theorem secondDiff_vanishes {φ : E → ℝ} {G : E → E} {R : ℝ}
    (hG : ∀ x, SupportingSlope φ x (G x))
    (hR : 0 < R) (hbound : ∀ x, ‖G x‖ ≤ R)
    (hdual : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) (h : E) {e : ℝ} (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, r ≤ ‖z‖ → secondDiff φ h z < e := by
  by_cases hh : h = 0
  · subst h
    refine ⟨1,by norm_num,?_⟩
    intro z _
    dsimp [secondDiff]
    simpa only [add_zero, sub_zero, show φ z+φ z-2*φ z=0 by ring] using he
  have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  let c : ℝ := 8*R*‖h‖^2
  have hcpos : 0 < c := by dsimp [c]; positivity
  obtain ⟨d,hd0,hd⟩ := exists_between (lt_min hR (div_pos (sq_pos_of_pos he) hcpos))
  have hdR : d < R := hd.trans_le (min_le_left _ _)
  have hdsmall : c*d < e^2 := by
    have hd' := hd.trans_le (min_le_right _ _)
    simpa only [mul_comm] using (lt_div_iff₀ hcpos).mp hd'
  let a : ℝ := R-d/2
  have ha : 0 < a := by dsimp [a]; linarith
  have haR : a < R := by dsimp [a]; linarith
  obtain ⟨b,hb,hlower⟩ := radial_lower_of_finite_dual ha haR hdual
  let C : ℝ := b+|φ 0|+2*R*‖h‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let r : ℝ := 2*C/d+1
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,hr,?_⟩
  intro z hz
  have hzn : 0 < ‖z‖ := hr.trans_le hz
  have hlarge : C ≤ (d/2)*‖z‖ := by
    have hh' := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ d/2)
    have heq : (d/2)*r = C+d/2 := by dsimp [r]; field_simp
    rw [heq] at hh'
    linarith
  have hlarge' (k : E) (hk : ‖k‖ = ‖h‖) :
      b+|φ 0|+(a+R)*‖k‖ ≤ (d/2)*‖z‖ := by
    rw [hk]
    dsimp [C, a] at hlarge ⊢
    nlinarith [mul_nonneg hd0.le hhn.le]
  have hp := slope_alignment hG hbound ha.le hlower hzn (hlarge' h rfl)
  have hm := slope_alignment hG hbound ha.le hlower hzn (hlarge' (-h) (norm_neg h))
  have hu : ‖‖z‖⁻¹ • z‖ = 1 := by
    simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hzn]
    exact inv_mul_cancel₀ (ne_of_gt hzn)
  have hp' : R-d ≤ ⟪G (z+h),‖z‖⁻¹ • z⟫_ℝ := by dsimp [a] at hp; linarith
  have hm' : R-d ≤ ⟪G (z-h),‖z‖⁻¹ • z⟫_ℝ := by
    rw [show a-d/2=R-d by dsimp [a]; ring] at hm
    simpa only [sub_eq_add_neg] using hm
  have hdiff := difference_alignment hu hR.le (hbound (z+h)) (hbound (z-h)) hp' hm'
  have hnonneg := secondDiff_nonneg hG h z
  have hupper := secondDiff_le_gradient hG h z
  have hsq := pow_le_pow_left₀ hnonneg hupper 2
  have hsq' := mul_le_mul_of_nonneg_right hdiff (sq_nonneg ‖h‖)
  dsimp [c] at hdsmall
  rw [mul_pow] at hsq
  nlinarith

end WeakMomentBound

namespace LogDetConcavity
open Matrix
open scoped MatrixOrder BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨Q,hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hQ]
  change 0 ≤ (Qᴴ * Q * B).trace
  rw [← Matrix.trace_mul_cycle Q B Qᴴ]
  exact (hB.mul_mul_conjTranspose_same Q).trace_nonneg

lemma logdet_le_trace {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card ι := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hA.eigenvalues_pos i))]
  calc
    _ ≤ ∑ i, (hA.isHermitian.eigenvalues i - 1) :=
      Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
    _ = _ := by simp [Finset.sum_sub_distrib]

theorem tangent {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det - Real.log A.det ≤ (A⁻¹ * (B-A)).trace := by
  obtain ⟨Q,hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.inv.posSemidef.nonneg
  have hQ' : A⁻¹ = Qᴴ * Q := hQ
  have hdQ : Q.det ≠ 0 := by
    have hd := congrArg Matrix.det hQ'
    rw [Matrix.det_mul, Matrix.det_conjTranspose] at hd
    intro hz
    simp only [hz, mul_zero] at hd
    exact ne_of_gt hA.inv.det_pos hd
  have hunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hdQ)
  have hK : (Q * B * Qᴴ).PosDef := hB.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr hunit)
  have ht := logdet_le_trace hK
  have htrace : (Q * B * Qᴴ).trace = (A⁻¹ * B).trace := by
    rw [hQ', Matrix.trace_mul_cycle]
  have hdet : (Q * B * Qᴴ).det = B.det / A.det := by
    have hd := congrArg Matrix.det hQ'
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at hd ⊢
    rw [div_eq_mul_inv, hd]
    ring
  rw [htrace, hdet, Real.log_div (ne_of_gt hB.det_pos) (ne_of_gt hA.det_pos)] at ht
  simpa only [Matrix.mul_sub, Matrix.trace_sub,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)), Matrix.trace_one] using ht

theorem midpoint_comparison {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (hmid : (2 • A - B - C).PosSemidef) :
    Real.log B.det + Real.log C.det - 2 * Real.log A.det ≤ 0 := by
  have hb := tangent hA hB
  have hc := tangent hA hC
  have hn := trace_mul_nonneg hA.inv.posSemidef hmid
  have he : (A⁻¹ * (2 • A - B - C)).trace =
      -((A⁻¹ * (B-A)).trace + (A⁻¹ * (C-A)).trace) := by
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos))]
    ring
  rw [he] at hn
  linarith

end LogDetConcavity
namespace WeakMomentBound
open CompactMomentVariational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma slopeMean_support {φ : E → ℝ} {P : E → E}
    (hs : ∀ z, SupportingSlope φ z (P z)) (h : E) (T : ℝ) (z : E) :
    SupportingSlope (shiftedMean φ h T) z (slopeMean P h z) := by
  intro y
  have hp := hs (z+h) (y+h)
  have hm := hs (z-h) (y-h)
  have ep : y+h-(z+h)=y-z := by abel
  have em : y-h-(z-h)=y-z := by abel
  rw [ep] at hp
  rw [em] at hm
  dsimp [shiftedMean,slopeMean]
  rw [real_inner_smul_left,inner_add_left]
  linarith

omit [InnerProductSpace ℝ E] in
lemma shiftedMean_continuous {φ : E → ℝ} (hc : Continuous φ) (h : E) (T : ℝ) :
    Continuous (shiftedMean φ h T) :=
  (((hc.comp (continuous_id.add_const h)).add (hc.comp (continuous_id.sub continuous_const))).sub
    continuous_const).div_const 2

lemma slopeMean_hasFDerivAt {P : E → E} {h z : E} {A B : E →L[ℝ] E}
    (hp : HasFDerivAt P A (z+h)) (hm : HasFDerivAt P B (z-h)) :
    HasFDerivAt (slopeMean P h) ((1/2:ℝ) • (A+B)) z := by
  have hp' : HasFDerivAt (fun y => P (y+h)) A z := by
    simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using hp.comp z ((hasFDerivAt_id z).add_const h)
  have hm' : HasFDerivAt (fun y => P (y-h)) B z := by
    simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using hm.comp z ((hasFDerivAt_id z).sub_const h)
  exact (hp'.add hm').const_smul (1/2:ℝ)

lemma shiftedMean_differentiableAt {φ : E → ℝ} {h z : E}
    (hp : DifferentiableAt ℝ φ (z+h)) (hm : DifferentiableAt ℝ φ (z-h)) (T : ℝ) :
    DifferentiableAt ℝ (shiftedMean φ h T) z :=
  by
  have hh := (((hp.comp z ((differentiableAt_id (𝕜 := ℝ)).add_const h)).add
    (hm.comp z ((differentiableAt_id (𝕜 := ℝ)).sub_const h))).sub_const T).mul_const (1/2:ℝ)
  change DifferentiableAt ℝ (fun y => (φ (y+h)+φ (y-h)-T)/2) z
  simpa only [div_eq_mul_inv,Function.comp_def,Pi.add_apply,id_eq,one_mul] using hh

variable [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
lemma inner_pos_of_matrix_posDef (b : OrthonormalBasis ι ℝ E) {H : E →L[ℝ] E}
    (hH : (LinearMap.toMatrix b.toBasis b.toBasis H.toLinearMap).PosDef) :
    ∀ v ≠ 0, 0 < ⟪H v,v⟫_ℝ := by
  intro v hv
  have hcoord : (b.toBasis.repr v : ι → ℝ) ≠ 0 := by
    intro he
    have hz : b.toBasis.repr v = 0 := DFunLike.coe_injective he
    exact hv (b.toBasis.repr.injective (by simpa using hz))
  have hh := hH.dotProduct_mulVec_pos hcoord
  rw [LinearMap.toMatrix_mulVec_repr] at hh
  have he (w : E) : (b.toBasis.repr w : ι → ℝ) = WithLp.ofLp (b.repr w) := by
    ext i
    exact b.coe_toBasis_repr_apply w i
  rw [he v] at hh
  change 0 < star (b.repr v).ofLp ⬝ᵥ (b.toBasis.repr (H v) : ι → ℝ) at hh
  rw [he (H v)] at hh
  have hi := b.repr.inner_map_map v (H v)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simp only [star_trivial] at hh hi
  rw [dotProduct_comm] at hi
  rw [hi] at hh
  simpa only [real_inner_comm] using hh

omit [Fintype ι] [DecidableEq ι] in
lemma mean_matrix_posDef {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    ((1/2:ℝ) • (A+B)).PosDef := (hA.add hB).smul (by norm_num)

lemma logdet_mean {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (Real.log A.det+Real.log B.det)/2 ≤ Real.log ((1/2:ℝ) • (A+B)).det := by
  have he : 2 • ((1/2:ℝ) • (A+B))-A-B=0 := by module
  have ht := LogDetConcavity.midpoint_comparison (mean_matrix_posDef hA hB) hA hB
    (by rw [he]; exact Matrix.PosSemidef.zero)
  linarith

omit [FiniteDimensional ℝ E] in
lemma matrix_slopeMean (b : OrthonormalBasis ι ℝ E) {P : E → E} {h z : E}
    (hp : DifferentiableAt ℝ P (z+h)) (hm : DifferentiableAt ℝ P (z-h)) :
    LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (slopeMean P h) z).toLinearMap =
      (1/2:ℝ) • (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ P (z+h)).toLinearMap+
        LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ P (z-h)).toLinearMap) := by
  rw [(slopeMean_hasFDerivAt hp.hasFDerivAt hm.hasFDerivAt).fderiv]
  simp

end WeakMomentBound
end

namespace WeakMomentBound

lemma finite_difference_gain {ε r d δ : ℝ} (hε : 0 < ε) (hr : 0 ≤ r)
    (hδ : δ ≤ d*r) (hlarge : 4/ε*r^2 < δ) : δ/2 < ε/8*d^2 := by
  have hrpos : 0 < r := by
    by_contra he
    have hz : r=0 := le_antisymm (le_of_not_gt he) hr
    rw [hz] at hδ hlarge
    norm_num at hδ hlarge
    linarith
  have hdlarge : 4*r/ε<d := (mul_lt_mul_iff_left₀ hrpos).mp (by
    calc
      (4*r/ε)*r = 4/ε*r^2 := by ring
      _ < δ := hlarge
      _ ≤ d*r := hδ)
  have hk : 0 < ε/8*d-r/2 := by
    have ht := (div_lt_iff₀ hε).mp hdlarge
    nlinarith
  have hdpos : 0 < d := (div_pos (mul_pos (by norm_num) hrpos) hε).trans hdlarge
  have ht := mul_pos hdpos hk
  nlinarith

lemma density_lt_of_logdet {d Z v φ : ℝ} (hd : 0 < d) (hZ : 0 < Z)
    (hh : v+Real.log Z-φ < Real.log d) :
    ENNReal.ofReal (Real.exp (-φ)) <
      ENNReal.ofReal |d| * ENNReal.ofReal (Real.exp (-v)/Z) := by
  rw [abs_of_pos hd,← ENNReal.ofReal_mul hd.le]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos _).le).mpr
  apply (Real.log_lt_log_iff (Real.exp_pos _) (mul_pos hd (div_pos (Real.exp_pos _) hZ))).mp
  rw [Real.log_exp,Real.log_mul hd.ne' (div_pos (Real.exp_pos _) hZ).ne',
    Real.log_div (Real.exp_ne_zero _) hZ.ne',Real.log_exp]
  linarith

end WeakMomentBound

noncomputable section
namespace CompactMomentVariational
open WeakMomentBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weak_secondDiff_cap (b : OrthonormalBasis ι ℝ E) {V φ : E → ℝ}
    (hV : Continuous V) {ε : ℝ} (hε : 0 < ε)
    (hcurv : ∀ x y, ε/8*‖x-y‖^2 ≤ (V x+V y)/2-V ((1/2:ℝ) • (x+y)))
    {R : ℝ≥0} (hR : 0 < R) (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      TruncatedMoment.target μ R V) (h z : E) :
    secondDiff φ h z ≤ 4/ε*‖h‖^2 := by
  let P := chosenSlope μ hc hl
  let Z := TruncatedMoment.partition μ R V
  let K := Metric.ball (0:E) (R:ℝ)
  let σ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))
  let ν := TruncatedMoment.target μ R V
  have hZ : 0 < Z := TruncatedMoment.partition_pos μ hV hR
  have hPs : ∀ x, SupportingSlope φ x (P x) := chosenSlope_support μ hc hl
  have hPbound : ∀ x, ‖P x‖ ≤ (R:ℝ) := norm_chosenSlope_le μ hc hl
  have hσμ : σ ≪ μ := withDensity_absolutelyContinuous _ _
  have hνμ : ν ≪ μ := (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hback := reverse_pushforward hσμ hνμ Metric.isOpen_ball (convex_ball (0:E) R) hc hl hb
    (TruncatedMoment.ae_mem_ball μ V R) hm
  have : IsProbabilityMeasure ν := TruncatedMoment.probability μ hV hR
  have hσuniv : σ univ=1 := by
    rw [← hback,Measure.map_apply (gradient_measurable _) MeasurableSet.univ]
    exact measure_univ
  have ha := ae_positive_MA μ b hV hR hc hl hb hm
  have hap := (measurePreserving_add_right μ h).quasiMeasurePreserving.ae ha
  have ham' := (measurePreserving_add_right μ (-h)).quasiMeasurePreserving.ae ha
  have ham : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ (x-h) ∧ DifferentiableAt ℝ P (x-h) ∧
      (weakHessian μ b hc hl (x-h)).PosDef ∧
      Real.log (weakHessian μ b hc hl (x-h)).det = V (P (x-h))+Real.log Z-φ (x-h) ∧
      P (x-h) ∈ K := by simpa only [sub_eq_add_neg] using ham'
  by_contra hnot
  obtain ⟨T,hT,hTz⟩ := exists_between (lt_of_not_ge hnot)
  have hTpos : 0 < T := (by positivity : (0:ℝ) ≤ 4/ε*‖h‖^2).trans_lt hT
  obtain ⟨r,hr,hinf⟩ := secondDiff_vanishes hPs hR hPbound hb h hTpos
  let s : ℝ := max r (‖z‖+1)
  let C := Metric.closedBall (0:E) s
  have hC : IsCompact C := isCompact_closedBall _ _
  let q := shiftedMean φ h T
  let Q := slopeMean P h
  have hqs : ∀ x, SupportingSlope q x (Q x) := slopeMean_support hPs h T
  have hqc : Continuous q := shiftedMean_continuous hl.continuous h T
  have hboundary : ∀ y ∈ frontier C, q y ≤ φ y := by
    intro y hy
    have hys : s ≤ ‖y‖ := by
      by_contra he
      have hym : y ∈ Metric.ball (0:E) s := by
        simpa only [Metric.mem_ball,dist_zero_right] using lt_of_not_ge he
      have hyint : y ∈ interior C := Metric.ball_subset_interior_closedBall hym
      exact (disjoint_interior_frontier (s := C)).notMem_of_mem_left hyint hy
    have hd := hinf y ((le_max_left _ _).trans hys)
    dsimp [q,shiftedMean,secondDiff] at hd ⊢
    linarith
  have hreg : ∀ᵐ x ∂μ, DifferentiableAt ℝ q x ∧ DifferentiableAt ℝ Q x ∧
      (∀ v ≠ 0, 0 < ⟪(fderiv ℝ Q x) v,v⟫_ℝ) ∧ Q x ∈ K := by
    filter_upwards [hap,ham] with x hp hm
    have hmtr := matrix_slopeMean b hp.2.1 hm.2.1
    have hpd : (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ Q x).toLinearMap).PosDef := by
      rw [hmtr]
      exact mean_matrix_posDef hp.2.2.1 hm.2.2.1
    refine ⟨shiftedMean_differentiableAt hp.1 hm.1 T,
      (slopeMean_hasFDerivAt hp.2.1.hasFDerivAt hm.2.1.hasFDerivAt).differentiableAt,
      inner_pos_of_matrix_posDef b hpd,?_⟩
    have hconv := (convex_ball (0:E) (R:ℝ)) hp.2.2.2.2 hm.2.2.2.2
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1:ℝ)/2+1/2=1)
    simpa only [Q,slopeMean,smul_add] using hconv
  have hstrict : ∀ᵐ x ∂μ, x ∈ interior C → φ x < q x →
      ENNReal.ofReal (Real.exp (-φ x)) < ENNReal.ofReal |(fderiv ℝ Q x).det| *
        ENNReal.ofReal (Real.exp (-V (gradient q x))/Z) := by
    filter_upwards [hap,ham] with x hp hm
    intro _ hx
    have hlarge : 4/ε*‖h‖^2 < secondDiff φ h x := by
      dsimp [q,shiftedMean] at hx
      dsimp [secondDiff]
      linarith
    have hgain := finite_difference_gain hε (norm_nonneg h)
      (secondDiff_le_gradient hPs h x) hlarge
    have hmtr := matrix_slopeMean b hp.2.1 hm.2.1
    have hpd := mean_matrix_posDef hp.2.2.1 hm.2.2.1
    have hld := logdet_mean hp.2.2.1 hm.2.2.1
    have hdet : (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ Q x).toLinearMap).det =
        (fderiv ℝ Q x).det := LinearMap.det_toMatrix b.toBasis _
    have hdetpos : 0 < (fderiv ℝ Q x).det := by
      rw [← hdet,hmtr]
      exact hpd.det_pos
    have hgradient : gradient q x=Q x := gradient_eq_of_support
      (shiftedMean_differentiableAt hp.1 hm.1 T) (hqs x)
    rw [hgradient]
    apply density_lt_of_logdet hdetpos hZ
    rw [← hdet,hmtr]
    have hcv := hcurv (P (x+h)) (P (x-h))
    dsimp [secondDiff] at hgain
    have hlogp := hp.2.2.2.1
    have hlogm := hm.2.2.2.1
    change Real.log (weakHessian μ b hc hl (x+h)).det =
      V (P (x+h))+Real.log Z-φ (x+h) at hlogp
    change V ((1/2:ℝ) • (P (x+h)+P (x-h)))+Real.log Z-φ x <
      Real.log ((1/2:ℝ) • (weakHessian μ b hc hl (x+h)+weakHessian μ b hc hl (x-h))).det
    linarith
  have hfinite : σ C ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono (subset_univ C)) (by
    rw [hσuniv]; exact ENNReal.one_lt_top))
  have hcomp := ae_strict_weighted_comparison μ Metric.isOpen_ball (convex_ball (0:E) R)
    hb hback hc hl.continuous hqc hqs hC hboundary hreg hfinite
    (hV.neg.rexp.measurable.div_const Z).ennreal_ofReal hstrict
  have hzC : z ∈ C := by
    change dist z 0 ≤ s
    rw [dist_zero_right]
    exact (by linarith : ‖z‖ ≤ ‖z‖+1).trans (le_max_right _ _)
  have hh := hcomp z hzC
  dsimp [q,shiftedMean,secondDiff] at hh hTz
  linarith

end CompactMomentVariational
namespace QuadraticRegularity
open Filter
open scoped Topology InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma remainder_of_secondDiff {φ : E → ℝ} {P : E → E} {C : ℝ}
    (hs : ∀ x y, φ x+⟪P x,y-x⟫_ℝ ≤ φ y)
    (hc : ∀ x h, φ (x+h)+φ (x-h)-2*φ x ≤ C*‖h‖^2) (x y : E) :
    |φ y-φ x-⟪P x,y-x⟫_ℝ| ≤ C*‖y-x‖^2 := by
  have hh := hc x (y-x)
  have hu := hs x (x-(y-x))
  have hl := hs x y
  have he : x+(y-x)=y := by abel
  have he' : x-(y-x)-x=-(y-x) := by abel
  rw [he] at hh
  rw [he',inner_neg_right] at hu
  rw [abs_of_nonneg (by linarith)]
  linarith

lemma hasFDerivAt_of_remainder {φ : E → ℝ} {P : E → E} {C : ℝ}
    (hc : ∀ x y, |φ y-φ x-⟪P x,y-x⟫_ℝ| ≤ C*‖y-x‖^2) (x : E) :
    HasFDerivAt φ (innerSL ℝ (P x)) x := by
  rw [hasFDerivAt_iff_isLittleO]
  have hh : (fun y => φ y-φ x-(innerSL ℝ (P x)) (y-x)) =O[𝓝 x]
      (fun y => ‖y-x‖^2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C,Filter.Eventually.of_forall fun y => ?_⟩
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖y-x‖),innerSL_apply_apply] using hc x y
  exact hh.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < (2:ℕ)))

lemma slope_difference_bound {φ : E → ℝ} {P : E → E} {C : ℝ} (hC : 0<C)
    (hs : ∀ x y, φ x+⟪P x,y-x⟫_ℝ ≤ φ y)
    (hu : ∀ x y, φ y ≤ φ x+⟪P x,y-x⟫_ℝ+C*‖y-x‖^2) (x y : E) :
    ‖P y-P x‖ ≤ (4*C)*‖y-x‖ := by
  let w := P y-P x
  let t := 1/(2*C)
  have ht : 0<t := by dsimp [t]; positivity
  have he (v : E) : ⟪w,v⟫_ℝ ≤ ⟪w,y-x⟫_ℝ+C*‖v‖^2 := by
    have hlo := hs x y
    have hmid := hs y (x+v)
    have hhi := hu x (x+v)
    have hid : x+v-y=v-(y-x) := by abel
    rw [hid,inner_sub_right] at hmid
    rw [add_sub_cancel_left] at hhi
    dsimp [w]
    simp only [inner_sub_left]
    linarith
  have hh := he (t • w)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,
    abs_of_pos ht] at hh
  have hi := real_inner_le_norm w (y-x)
  have halg : t-C*t^2=1/(4*C) := by dsimp [t]; field_simp; ring
  have hb : 1/(4*C)*‖w‖^2 ≤ ‖w‖*‖y-x‖ := by nlinarith
  have hc4 : 0<4*C := by positivity
  have hm := mul_le_mul_of_nonneg_left hb hc4.le
  have heq : (4*C)*(1/(4*C))=1 := by field_simp
  rw [← mul_assoc,heq,one_mul] at hm
  change ‖w‖ ≤ (4*C)*‖y-x‖
  by_cases hw : ‖w‖=0
  · rw [hw]; positivity
  · have hp : 0<‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    nlinarith

lemma lipschitz_of_remainder {φ : E → ℝ} {P : E → E} {C : ℝ≥0} (hC : 0<C)
    (hs : ∀ x y, φ x+⟪P x,y-x⟫_ℝ ≤ φ y)
    (hc : ∀ x y, |φ y-φ x-⟪P x,y-x⟫_ℝ| ≤ C*‖y-x‖^2) :
    LipschitzWith (4*C) P := by
  apply LipschitzWith.of_dist_le_mul
  intro y x
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_ofNat]
  apply slope_difference_bound (by exact hC) hs
  intro x y
  have hh := (le_abs_self (φ y-φ x-⟪P x,y-x⟫_ℝ)).trans (hc x y)
  linarith

lemma contDiff_one_of_remainder {φ : E → ℝ} {P : E → E} {C : ℝ≥0} (hC : 0<C)
    (hs : ∀ x y, φ x+⟪P x,y-x⟫_ℝ ≤ φ y)
    (hc : ∀ x y, |φ y-φ x-⟪P x,y-x⟫_ℝ| ≤ C*‖y-x‖^2) :
    ContDiff ℝ 1 φ := by
  have hd := hasFDerivAt_of_remainder hc
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hd x).differentiableAt,?_⟩
  have he : fderiv ℝ φ = fun x => innerSL ℝ (P x) := funext fun x => (hd x).fderiv
  rw [he]
  exact (innerSL ℝ).continuous.comp (lipschitz_of_remainder hC hs hc).continuous

end QuadraticRegularity
namespace CompactMomentVariational
open WeakMomentBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weak_contDiff_one (b : OrthonormalBasis ι ℝ E) {V φ : E → ℝ}
    (hV : Continuous V) {ε : ℝ} (hε : 0 < ε)
    (hcurv : ∀ x y, ε/8*‖x-y‖^2 ≤ (V x+V y)/2-V ((1/2:ℝ) • (x+y)))
    {R : ℝ≥0} (hR : 0 < R) (hc : ConvexOn ℝ univ φ) (hl : LipschitzWith R φ)
    (hb : ∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ))
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      TruncatedMoment.target μ R V) :
    ContDiff ℝ 1 φ ∧ LipschitzWith (Real.toNNReal (16/ε)) (gradient φ) := by
  let C : ℝ≥0 := Real.toNNReal (4/ε)
  have hC : 0<C := Real.toNNReal_pos.mpr (by positivity)
  have heC : (C:ℝ)=4/ε := Real.coe_toNNReal _ (by positivity)
  let P := chosenSlope μ hc hl
  have hs : ∀ x y, φ x+⟪P x,y-x⟫_ℝ ≤ φ y := chosenSlope_support μ hc hl
  have hd : ∀ x h, φ (x+h)+φ (x-h)-2*φ x ≤ (C:ℝ)*‖h‖^2 := by
    intro x h
    rw [heC]
    exact weak_secondDiff_cap μ b hV hε hcurv hR hc hl hb hm h x
  have hr := QuadraticRegularity.remainder_of_secondDiff hs hd
  have hf := QuadraticRegularity.hasFDerivAt_of_remainder hr
  have he : gradient φ=P := funext fun x => gradient_eq_of_support
    ((hf x).differentiableAt) (hs x)
  refine ⟨QuadraticRegularity.contDiff_one_of_remainder hC hs hr,?_⟩
  rw [he]
  have hnum : 4*C=Real.toNNReal (16/ε) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul,NNReal.coe_ofNat,heC,Real.coe_toNNReal _ (by positivity)]
    ring
  rw [← hnum]
  exact QuadraticRegularity.lipschitz_of_remainder hC hs hr

theorem exists_C11_truncated_oai (b : OrthonormalBasis ι ℝ E)
    {V : E → ℝ} (hV : Continuous V) (hVe : Function.Even V)
    {ε : ℝ} (hε : 0 < ε)
    (hcurv : ∀ x y, ε/8*‖x-y‖^2 ≤ (V x+V y)/2-V ((1/2:ℝ) • (x+y)))
    {R : ℝ≥0} (hR : 0 < R) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Function.Even φ ∧ LipschitzWith R φ ∧
      ContDiff ℝ 1 φ ∧ LipschitzWith (Real.toNNReal (16/ε)) (gradient φ) ∧
      (∀ h z, secondDiff φ h z ≤ 4/ε*‖h‖^2) ∧
      (∃ c > 0, ∃ d : ℝ, ∀ z, c*‖z‖-d ≤ φ z) ∧
      IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) ∧
      (∀ x ∈ Metric.ball (0:E) R, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) ∧
      Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
        TruncatedMoment.target μ R V := by
  obtain ⟨φ,hc,he,hl,ht,hp,hb,hm,_⟩ := exists_weak_truncated_MA μ hV hVe hR
  have hr := weak_contDiff_one μ b hV hε hcurv hR hc hl hb hm
  exact ⟨φ,hc,he,hl,hr.1,hr.2,weak_secondDiff_cap μ b hV hε hcurv hR hc hl hb hm,
    ht,hp,hb,hm⟩

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CompactMomentVariational.exists_C11_truncated_oai.{u_1, u_2} := @OAI.CompactMomentVariational.exists_C11_truncated_oai.{u_1, u_2}
