-- Prove2me | solution 1 for MomentSearch.rakhmanov_off_node_cauchy_formula
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:18:02.523351+00:00
-- url     : https://prove2.me/submissions/d044245a-5ed5-422d-b283-3a78246829a9

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_quantile_real_regularization
import Theorems.Thm_MomentSearch_rakhmanov_lower_half_plane_deformation

open Set Filter MeasureTheory
open scoped Topology

private theorem continuousAtCauchy {A Z : ℝ → ℂ} {x : ℂ} (hZ : Continuous Z)
    (hA : IntervalIntegrable A volume 0 2)
    (hne : ∀ t ∈ Icc (0:ℝ) 2, (x:ℂ) ≠ Z t) :
    ContinuousAt (fun u : ℂ => ∫ t in (0:ℝ)..2, A t / ((u:ℂ)-Z t)) x := by
  obtain ⟨p,hp,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0:ℝ) 2).Nonempty from ⟨0,by norm_num⟩)
    (show Continuous (fun t => ‖(x:ℂ)-Z t‖) by fun_prop).continuousOn
  let m := ‖(x:ℂ)-Z p‖
  have hm : 0 < m := norm_pos_iff.mpr (sub_ne_zero.mpr (hne p hp))
  have far {u : ℂ} {t : ℝ} (hu : dist u x < m/2) (ht : t ∈ Icc (0:ℝ) 2) :
      m/2 ≤ ‖(u:ℂ)-Z t‖ := by
    have hl : m ≤ ‖(x:ℂ)-Z t‖ := hmin ht
    have hh := norm_add_le ((x:ℂ)-u) ((u:ℂ)-Z t)
    rw [sub_add_sub_cancel] at hh
    rw [dist_comm, dist_eq_norm] at hu
    linarith
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun t => ‖A t‖ * (m/2)⁻¹)
  · exact .of_forall fun u => (hA.def'.1.aemeasurable.div
      ((continuous_const.sub hZ).aemeasurable)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x (show 0 < m / 2 by positivity)] with u hu
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    rw [norm_div, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (far hu ⟨ht.1.le,ht.2⟩)
  · exact hA.norm.mul_const _
  · apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    exact continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr (hne _ ⟨ht.1.le,ht.2⟩))

private theorem logHeightLimit (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun h : ℝ => Real.log ‖(x:ℂ) - (h:ℂ)*Complex.I‖) (𝓝[>] 0) (𝓝 (Real.log |x|)) := by
  have hc : ContinuousAt (fun h : ℝ => ‖(x:ℂ) - (h:ℂ)*Complex.I‖) 0 := by fun_prop
  have hl := hc.log (by simpa using hx)
  simpa using (hl.continuousWithinAt (s := Ioi 0)).tendsto

private theorem logPotentialLimit (ρ : ℝ → ℝ) (hc : Continuous ρ) (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    Tendsto (fun h : ℝ => ∫ t in (-1:ℝ)..1,
      Real.log ‖((x-t:ℝ):ℂ) - (h:ℂ)*Complex.I‖ * ρ t) (𝓝[>] 0)
      (𝓝 (∫ t in (-1:ℝ)..1, Real.log |x-t| * ρ t)) := by
  let b := fun t => (|Real.log (x-t)| + Real.log 3) * |ρ t|
  have hi : IntervalIntegrable (fun t => Real.log (x-t)) volume (-1) 1 := by
    convert! (intervalIntegral.intervalIntegrable_log' (a := x-(-1)) (b := x-1)).comp_sub_left x using 1 <;> ring
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence b
  · exact .of_forall fun h => ((Real.measurable_log.comp (by fun_prop)).mul hc.measurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with h hp hl
    filter_upwards [volume.ae_ne x] with t ht
    intro htI
    rw [uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at htI
    have hd : 0 < |x-t| := abs_pos.mpr (sub_ne_zero.mpr ht.symm)
    let v := ((x-t:ℝ):ℂ) - (h:ℂ)*Complex.I
    have low : |x-t| ≤ ‖v‖ := by simpa [v] using Complex.abs_re_le_norm v
    have high : ‖v‖ ≤ 3 := by
      have hh := norm_sub_le ((x-t:ℝ):ℂ) ((h:ℂ)*Complex.I)
      have h0 : 0 < h := hp
      have h1 : h < 1 := hl
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,abs_of_pos h0] at hh
      have h2 : |x-t| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1,htI.2],by linarith [hx.2,htI.1]⟩
      linarith
    have lower := Real.log_le_log hd low
    rw [Real.log_abs] at lower
    have upper := Real.log_le_log (hd.trans_le low) high
    have ha : |Real.log ‖v‖| ≤ |Real.log (x-t)| + Real.log 3 := by
      apply abs_le.mpr
      constructor <;> linarith [abs_nonneg (Real.log (x-t)),neg_abs_le (Real.log (x-t)), Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
    exact (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
  · exact (hi.abs.add intervalIntegrable_const).mul_continuousOn hc.abs.continuousOn
  · filter_upwards [volume.ae_ne x] with t ht
    intro _
    exact (logHeightLimit _ (sub_ne_zero.mpr ht.symm)).mul_const _

private theorem massIntegral (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (har : r^2+a^2=1) :
    (∫ x in (-r)..r, Real.arctan (Real.sqrt (r^2-x^2)/a)) = Real.pi*(1-a) := by
  let S (x : ℝ) := Real.sqrt (r^2-x^2)
  let W (x : ℝ) := Real.sqrt (1-x^2)
  let A (x : ℝ) := Real.arctan (S x/a)
  let G (x : ℝ) := x*A x + Real.arcsin (a*x/(r*W x)) - a*Real.arcsin (x/r)
  have wpos (x : ℝ) (hx : x ∈ Icc (-r) r) : 0 < W x := by
    apply Real.sqrt_pos.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ r+x by linarith [hx.1]),sq_pos_of_pos ha]
  have cg : ContinuousOn G (Icc (-r) r) := by
    have d : ContinuousOn (fun x => a*x/(r*W x)) (Icc (-r) r) :=
      (continuous_const.mul continuous_id).continuousOn.div
        (show Continuous (fun x => r*W x) by dsimp [W]; fun_prop).continuousOn
        (fun x hx => (mul_pos hr (wpos x hx)).ne')
    have ca : Continuous A := by dsimp [A,S]; fun_prop
    exact ((continuous_id.mul ca).continuousOn.add (Real.continuous_arcsin.comp_continuousOn d)).sub
      (show Continuous (fun x => a*Real.arcsin (x/r)) by fun_prop).continuousOn
  have dg (x : ℝ) (hx : x ∈ Ioo (-r) r) : HasDerivAt G (A x) x := by
    have hs0 : 0 < r^2-x^2 := by
      nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0<r+x by linarith [hx.1])]
    have hs : 0 < S x := Real.sqrt_pos.mpr hs0
    have hw := wpos x ⟨hx.1.le,hx.2.le⟩
    have hss : S x ^ 2 = r^2-x^2 := Real.sq_sqrt hs0.le
    have hww : W x ^ 2 = 1-x^2 := Real.sq_sqrt (Real.sqrt_pos.mp hw).le
    have hden : r^2*(W x)^2 - (a*x)^2 = (S x)^2 := by
      rw [hww,hss]
      linear_combination -x^2*har
    have ds : HasDerivAt S (-x/S x) x := by
      convert! (((hasDerivAt_id x).pow 2).const_sub (r^2)).sqrt hs0.ne' using 1
      dsimp [S]; ring
    have dw : HasDerivAt W (-x/W x) x := by
      convert! (((hasDerivAt_id x).pow 2).const_sub 1).sqrt (Real.sqrt_pos.mp hw).ne' using 1
      dsimp [W]; ring
    have da : HasDerivAt A (-a*x/(S x * W x^2)) x := by
      convert! (Real.hasDerivAt_arctan (S x/a)).comp x (ds.div_const a) using 1
      have hd : a^2 + (S x)^2 = (W x)^2 := by linarith
      field_simp [ha.ne',hs.ne',hw.ne']
      linear_combination -x*hd
    have dq : HasDerivAt (fun u => a*u/(r*W u)) (a/(r*W x^3)) x := by
      convert! (((hasDerivAt_id x).const_mul a).div (dw.const_mul r) (mul_pos hr hw).ne') using 1
      field_simp [hr.ne',hw.ne']
      simp only [id_eq]
      linear_combination -hww
    have root {u v : ℝ} (hv : 0<v) (h : 1-u^2=v^2) :
        u ≠ -1 ∧ u ≠ 1 ∧ Real.sqrt (1-u^2)=v := by
      exact ⟨by rintro rfl; nlinarith [sq_pos_of_pos hv],
        by rintro rfl; nlinarith [sq_pos_of_pos hv],by rw [h,Real.sqrt_sq hv.le]⟩
    obtain ⟨hq1,hq2,hq⟩ := root (u := a*x/(r*W x)) (div_pos hs (mul_pos hr hw)) (by
      field_simp [hr.ne',hw.ne']; linarith only [hden])
    obtain ⟨ht1,ht2,ht⟩ := root (u := x/r) (div_pos hs hr) (by
      field_simp [hr.ne']; linarith only [hss])
    have dg' := (((hasDerivAt_id x).mul da).add
      ((Real.hasDerivAt_arcsin hq1 hq2).comp x dq)).sub
      (((Real.hasDerivAt_arcsin ht1 ht2).comp x ((hasDerivAt_id x).div_const r)).const_mul a)
    convert! dg' using 1
    rw [hq,ht]
    simp only [id_eq,one_mul]
    field_simp [hr.ne',hs.ne',hw.ne']
    linear_combination a*hww
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show -r ≤ r by linarith)
    cg dg (Continuous.intervalIntegrable (u := A) (by dsimp [A,S]; fun_prop) ..)
  have wr : W r = a := by dsimp [W]; rw [show 1-r^2=a^2 by linarith,Real.sqrt_sq ha.le]
  have wr' : W (-r) = a := by simpa [W] using wr
  have ar : A r = 0 := by simp [A,S]
  have ar' : A (-r) = 0 := by simp [A,S]
  change (∫ x in (-r)..r, A x) = _
  rw [hint]
  dsimp only [G]
  rw [wr,wr',ar,ar',show a*r/(r*a)=1 by field_simp,show a*(-r)/(r*a)= -1 by field_simp]
  simp [hr.ne', Real.arcsin_neg, Real.arcsin_one]
  ring

private theorem exteriorPhase (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    ∀ z : ℝ, z ∉ Ioo (-r) r → |f z| = 1 := by
  intro r ρ f
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have cf : Continuous ρ := by dsimp [ρ]; fun_prop
  have nn (u : ℝ) : 0 ≤ ρ u := by
    dsimp [ρ]; exact mul_nonneg (by positivity) (Real.arctan_nonneg.mpr (by positivity))
  let F := fun u : ℝ => ∫ t in (-r)..u, ρ t
  have cont : Continuous F := intervalIntegral.continuous_primitive (fun a b => cf.intervalIntegrable a b) _
  have inc (u v : ℝ) : F u + (∫ t in u..v, ρ t) = F v :=
    intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable ..) (cf.intervalIntegrable ..)
  have mono : Monotone F := fun u v huv => by
    linarith [inc u v, intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) huv nn]
  have h0 : F (-r) = 0 := by simp [F]
  have htot : F r = (N : ℝ) - k  := by
    let c : ℝ := (k:ℝ)/N
    have hc : 0 < c := div_pos hk' hN
    have hcr : c < 1 := (div_lt_one hN).mpr (by exact_mod_cast hkN)
    have hrdef : r = Real.sqrt (1-c^2) := by simp only [r,c,div_pow]
    have hv : 0 < 1-c^2 := by nlinarith [mul_pos (sub_pos.mpr hcr) (show 0<1+c by positivity)]
    have hr : 0 < r := hrdef ▸ Real.sqrt_pos.mpr hv
    have har : r^2+c^2=1 := by rw [hrdef, Real.sq_sqrt hv.le]; ring
    have hrat (z : ℝ) : (N:ℝ)/k*z = z/c := by dsimp [c]; field_simp
    dsimp [F,ρ]
    simp_rw [hrat]
    rw [intervalIntegral.integral_const_mul, massIntegral c r hc hr har]
    dsimp [c]; field_simp
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [div_nonneg (sq_nonneg (k:ℝ)) (sq_nonneg (N:ℝ))]⟩
  have htail : (∫ t in r..1, ρ t) = 0 := by
    have hzero : Set.EqOn ρ (fun _ => 0) (Set.uIcc r 1) := by
      rw [Set.uIcc_of_le hr1]
      intro u hu
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have huv : r^2-u^2 ≤ 0 := by nlinarith [sq_le_sq' (by linarith [hu.1]) hu.1]
      simp [ρ, Real.sqrt_eq_zero_of_nonpos huv]
    simpa using intervalIntegral.integral_congr (μ := MeasureTheory.volume) hzero
  let m := N-k
  have hm : (m:ℝ) = (N:ℝ)-k := Nat.cast_sub hkN.le
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have zeroOutside (z : ℝ) (hz : z ∉ Ioo (-r) r) : ρ z = 0 := by
    have hh : r^2-z^2 ≤ 0 := by
      by_cases hl : -r < z
      · have hzr : r ≤ z := le_of_not_gt (fun h => hz ⟨hl,h⟩)
        nlinarith [sq_le_sq' (by linarith) hzr]
      · have hzr := le_of_not_gt hl
        nlinarith [sq_le_sq' (a := r) (b := -z) (by linarith) (by linarith)]
    simp [ρ,Real.sqrt_eq_zero_of_nonpos hh]
  let T := fun z : ℝ => ∫ u in z..1, ρ u
  have tr : T r = 0 := htail
  have tl : T (-r) = m := by change F 1 = _; linarith [inc r 1]
  have outside (z : ℝ) (hz : z ∉ Ioo (-r) r) : T z = 0 ∨ T z = m := by
    by_cases h : r ≤ z
    · left
      have e : (∫ t in r..z, ρ t) = 0 := by
        have hh : Set.EqOn ρ (fun _ => 0) (uIcc r z) := by
          rw [uIcc_of_le h]; intro t ht; exact zeroOutside _ (fun e => (not_lt_of_ge ht.1) e.2)
        simpa using intervalIntegral.integral_congr (μ := volume) hh
      have hh := intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable r z) (cf.intervalIntegrable z 1) (μ := volume)
      change (∫ t in z..1, ρ t) = 0; linarith
    · right
      have h' : z ≤ -r := le_of_not_gt (fun hl => hz ⟨hl,lt_of_not_ge h⟩)
      have e : (∫ t in z..(-r), ρ t) = 0 := by
        have hh : Set.EqOn ρ (fun _ => 0) (uIcc z (-r)) := by
          rw [uIcc_of_le h']; intro t ht; exact zeroOutside _ (fun e => (not_lt_of_ge ht.2) e.1)
        simpa using intervalIntegral.integral_congr (μ := volume) hh
      have hh := intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable z (-r)) (cf.intervalIntegrable (-r) 1) (μ := volume)
      change (∫ t in (-r)..1, ρ t) = _ at tl
      change (∫ t in z..1, ρ t) = _; linarith
  intro z hz
  change |Real.cos (Real.pi*T z)| = 1
  rcases outside z hz with h | h
  · simp [h]
  · rw [h,mul_comm,Real.cos_nat_mul_pi,abs_pow]; simp

private theorem scaledPoisson (a b z : ℝ) (hab : a ≤ b) (G : ℝ → ℝ)
    (hG : IntegrableOn G (Ioc a b)) (hc : ContinuousAt ((Ioc a b).indicator G) z) :
    Tendsto (fun h : ℝ => (∫ t in a..b, h/((z-t)^2+h^2) * G t)/Real.pi)
      (𝓝[>] 0) (𝓝 ((Ioc a b).indicator G z)) := by
  let K := fun x : ℝ => (1+x^2)⁻¹ / Real.pi
  have hnorm : ∫ x, K x = 1 := by
    dsimp [K]; rw [integral_div,integral_univ_inv_one_add_sq,div_self Real.pi_ne_zero]
  have decay : Tendsto (fun x : ℝ => ‖x‖ ^ Module.finrank ℝ ℝ * K x)
      (Bornology.cobounded ℝ) (𝓝 0) := by
    simp only [Module.finrank_self,pow_one]
    have lim := tendsto_const_nhds.div_atTop (tendsto_norm_cobounded_atTop (E := ℝ)) (a := (1:ℝ))
    apply squeeze_zero' (Eventually.of_forall (fun _ => mul_nonneg (norm_nonneg _) (by dsimp [K]; positivity))) _ lim
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop (0:ℝ)] with x hx
    rw [le_div_iff₀ hx]
    dsimp [K]
    simp only [Real.norm_eq_abs] at *
    have hp := Real.pi_gt_three
    have hq : 0 < 1+x^2 := by positivity
    field_simp
    nlinarith [sq_abs x, mul_nonneg (sq_nonneg x) (show 0 ≤ Real.pi-1 by linarith)]
  have h := tendsto_integral_comp_smul_smul_of_integrable' (μ := volume) (φ := K)
    (fun x => by dsimp [K]; positivity) hnorm decay (hG.integrable_indicator measurableSet_Ioc) hc
  apply (h.comp tendsto_inv_nhdsGT_zero).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < h := hh
  dsimp only [Function.comp_apply]
  rw [intervalIntegral.integral_of_le hab, ← integral_div,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Ioc a b
  · simp only [Set.indicator_of_mem ht,Module.finrank_self,pow_one,smul_eq_mul,K]
    field_simp
    ring
  · simp [Set.indicator_of_notMem ht]

private theorem phaseLogIntegrable (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ)^2/(N : ℝ)^2)
    let ρ : ℝ → ℝ := fun t => (N : ℝ)/Real.pi * Real.arctan ((N : ℝ)/k * Real.sqrt (r^2-t^2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    IntegrableOn (fun z => Real.log (2*|f z|)) (Ioc (-r) r) := by
  intro r ρ f
  obtain ⟨_,Y,_,_,hzero,g,hg,hprod⟩ := MomentSearch.rakhmanov_quantile_real_regularization N k hk hkN
  have hr1 : r ≤ 1 := by
    dsimp [r]; rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [div_nonneg (sq_nonneg (k:ℝ)) (sq_nonneg (N:ℝ))]⟩
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have sub : Icc (-r) r ⊆ Icc (-1:ℝ) 1 := Icc_subset_Icc (neg_le_neg hr1) hr1
  have logs (y : ℝ) : IntegrableOn (fun t : ℝ => Real.log |t-y|) (Ioc (-r) r) := by
    simp only [Real.log_abs]
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (show -r ≤ r by linarith)).mp
    convert! (intervalIntegral.intervalIntegrable_log' (a := -r-y) (b := r-y)).comp_sub_right y using 1 <;> ring
  have hi : IntegrableOn (fun t : ℝ => Real.log 2 + (∑ y ∈ Y, Real.log |t-y|) - Real.log (g t)) (Ioc (-r) r) :=
    ((integrableOn_const (by simp)).add (integrable_finsetSum _ (fun y _ => logs y))).sub
      (((hg.log (fun z hz => (hprod z hz).1.ne')).mono sub).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (μ := volume)
    (show ∀ᵐ t ∂volume, t ∉ Y from (compl_mem_ae_iff.mpr (Y.finite_toSet.measure_zero volume)))] with t ht hy
  have ht' := sub (Ioc_subset_Icc_self ht)
  have hf : f t ≠ 0 := fun he => hy ((hzero t ht').mpr he)
  have he := congrArg (fun v : ℝ => Real.log |v|) (hprod t ht').2
  change Real.log |∏ y ∈ Y, (t-y)| = Real.log |g t * f t| at he
  have hn (y : ℝ) (h : y ∈ Y) : |t-y| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (fun e => hy (e ▸ h)))
  simp only [Finset.abs_prod,Real.log_prod hn,
    abs_mul,abs_of_pos (hprod t ht').1,Real.log_mul (hprod t ht').1.ne' (abs_ne_zero.mpr hf)] at he
  rw [Real.log_mul (by norm_num) (abs_ne_zero.mpr hf)]
  dsimp only at *
  linarith only [he]

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let η : ℝ → ℝ := fun x => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi
    IntervalIntegrable (fun t : ℝ => Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s))
      MeasureTheory.volume 0 2 ∧
    ∀ Y : Finset ℝ, Y.card = N-k → (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) →
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) →
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∉ Y → z ≠ r → z ≠ -r →
        (∑ y ∈ Y, Real.log |z-y|) + V z - Real.log |f z| =
          (if |z| < r then Real.log 2 else 0) + η z + η (-z) := by 
  intro r ρ f V s Z B η
  let A := fun t : ℝ => Complex.log (1 + Complex.exp (-(B t))) * (-(r:ℂ)*s)
  let E := fun x h : ℝ => (∫ t in (0:ℝ)..2, A t / ((x:ℂ)-(h:ℂ)*Complex.I-Z t)).im / Real.pi
  let L := fun v h : ℝ => Real.log ‖(v:ℂ)-(h:ℂ)*Complex.I‖
  let P := fun x h : ℝ => (∫ t in (-r)..r, h/((x-t)^2+h^2)*Real.log (2*|f t|))/Real.pi
  obtain ⟨hA,hoff⟩ := MomentSearch.rakhmanov_lower_half_plane_deformation N k hk hkN
  refine ⟨hA,?_⟩
  intro Y hcard hnodes hzeros z hz hy hr hl
  have contour (x : ℝ) (hx : x ≠ r) : Tendsto (E x) (𝓝[>] 0) (𝓝 (η x)) := by
    have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : (x:ℂ) ≠ Z t := by
      intro he
      have him := congrArg Complex.im he
      simp [Z,s,Complex.mul_im,Complex.mul_re] at him
      by_cases ht0 : t = 0
      · subst t; exact hx (by simpa [Z] using he)
      · have h0 : r = 0 := by
          have htpos := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have hsq : 0 < Real.sqrt 3 := by positivity
          rcases him with h | h <;> simp_all
        exact hx (by simpa [Z,h0] using he)
    have hu := continuousAtCauchy (A := A) (Z := Z) (by dsimp [Z]; fun_prop) hA hne
    have hg : Tendsto (fun h : ℝ => (x:ℂ)-(h:ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (x:ℂ)) := by
      have hg' : ContinuousAt (fun h : ℝ => (x:ℂ)-(h:ℂ)*Complex.I) 0 := by fun_prop
      simpa using (hg'.continuousWithinAt (s := Ioi 0)).tendsto
    exact ((Complex.continuous_im.continuousAt.tendsto.comp (hu.tendsto.comp hg)).div_const Real.pi)
  have hs : Tendsto (fun h => ∑ y ∈ Y, L (z-y) h) (𝓝[>] 0)
      (𝓝 (∑ y ∈ Y, Real.log |z-y|)) :=
    tendsto_finsetSum _ fun y h => logHeightLimit _ (sub_ne_zero.mpr (fun he => hy (he ▸ h)))
  have hρ : Continuous ρ := by dsimp [ρ]; fun_prop
  have hv := logPotentialLimit ρ hρ z hz
  have hcf : Continuous f := by
    have hρ : Continuous ρ := by dsimp [ρ]; fun_prop
    have hi : Continuous (fun z : ℝ => ∫ t in z..1, ρ t) :=
      continuous_iff_continuousAt.mpr (fun z => (intervalIntegral.integral_hasDerivAt_left
        (hρ.intervalIntegrable z 1) hρ.stronglyMeasurable.stronglyMeasurableAtFilter hρ.continuousAt).continuousAt)
    dsimp [f]; fun_prop
  have hp : Tendsto (P z) (𝓝[>] 0) (𝓝 ((if |z| < r then Real.log 2 else 0) + Real.log |f z|)) := by
    let G := fun t : ℝ => Real.log (2*|f t|)
    have hf : f z ≠ 0 := fun e => hy ((hzeros z hz).mpr e)
    have hg : ContinuousAt G z :=
      (continuousAt_const.mul hcf.abs.continuousAt).log (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hf))
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hi : IntegrableOn G (Ioc (-r) r) := phaseLogIntegrable N k hk hkN
    by_cases h : |z| < r
    · have hmem := abs_lt.mp h
      have hc : ContinuousAt ((Ioc (-r) r).indicator G) z := hg.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with u hu
        exact Set.indicator_of_mem (show u ∈ Ioc (-r) r from ⟨hu.1,hu.2.le⟩) G)
      have hp := scaledPoisson (-r) r z (by linarith) G hi hc
      rw [Set.indicator_of_mem (show z ∈ Ioc (-r) r from ⟨hmem.1,hmem.2.le⟩)] at hp
      rw [if_pos h]
      simpa only [P,G,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (abs_ne_zero.mpr hf)] using hp
    · have hout : z ∉ Icc (-r) r := by
        intro hz'; exact h (abs_lt.mpr ⟨lt_of_le_of_ne hz'.1 hl.symm,lt_of_le_of_ne hz'.2 hr⟩)
      have hc : ContinuousAt ((Ioc (-r) r).indicator G) z :=
        continuousAt_const.congr_of_eventuallyEq (by
          filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with u hu
          exact Set.indicator_of_notMem (fun h => hu (Ioc_subset_Icc_self h)) G)
      have hp := scaledPoisson (-r) r z (by linarith) G hi hc
      have hext := exteriorPhase N k hk hkN z (fun hh => hout (Ioo_subset_Icc_self hh))
      change |f z| = 1 at hext
      simpa only [Set.indicator_of_notMem (fun h => hout (Ioc_subset_Icc_self h)),if_neg h,hext,Real.log_one,zero_add] using hp
  have hlim := (hp.add (contour z hr)).add (contour (-z) (by intro he; apply hl; linarith))
  have heq := (hs.sub hv).congr' (show (fun h => (∑ y ∈ Y, L (z-y) h) -
      (∫ t in (-1:ℝ)..1, L (z-t) h * ρ t)) =ᶠ[𝓝[>] 0] (fun h => P z h + E z h + E (-z) h) by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hoff Y hcard hnodes hzeros z hz hy hr hl h hh)
  have ident := tendsto_nhds_unique heq hlim
  have hV : V z = -(∫ t in (-1:ℝ)..1, Real.log |z-t| * ρ t) := by
    dsimp [V]
    simp only [one_div,Real.log_inv,neg_mul,intervalIntegral.integral_neg]
  rw [hV]
  linarith only [ident]
