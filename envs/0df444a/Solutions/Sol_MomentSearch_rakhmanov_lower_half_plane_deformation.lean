-- Prove2me | solution 1 for MomentSearch.rakhmanov_lower_half_plane_deformation
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:24:53.385362+00:00
-- url     : https://prove2.me/submissions/c971d58d-32e2-40ee-a476-b0cbd57d5f47

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_triangle_phase_geometry
import Theorems.Thm_MomentSearch_rakhmanov_triangle_logarithm_trace

open Set MeasureTheory


namespace MomentSearch

/-- Pairing the tail discrepancy against the derivative of a test function.
The mass condition cancels the left endpoint term. -/
theorem quantile_tail_integration_by_parts (a b : ℝ) (hab : a ≤ b)
    (Y : Finset ℝ) (hY : ∀ y ∈ Y, y ∈ Icc a b)
    (ρ U K : ℝ → ℝ) (hρ : Continuous ρ) (hK : Continuous K)
    (hd : ∀ t, HasDerivAt U (K t) t)
    (mass : (∫ t in a..b, ρ t) = Y.card) :
    (∫ t in a..b, ((∑ y ∈ Y, if t ≤ y then (1 : ℝ) else 0) -
      (∫ u in t..b, ρ u)) * K t) =
      (∑ y ∈ Y, U y) - ∫ t in a..b, U t * ρ t := by
  let T := fun t : ℝ => ∫ u in t..b, ρ u
  have dT (t : ℝ) : HasDerivAt T (-ρ t) t :=
    intervalIntegral.integral_hasDerivAt_left (hρ.intervalIntegrable t b)
      hρ.stronglyMeasurable.stronglyMeasurableAtFilter hρ.continuousAt
  have cT : Continuous T := continuous_iff_continuousAt.mpr fun t => (dT t).continuousAt
  have cU : Continuous U := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    cT.continuousOn cU.continuousOn (fun t _ => dT t) (fun t _ => hd t)
    (hρ.neg.intervalIntegrable a b) (hK.intervalIntegrable a b)
  let J := fun (y t : ℝ) => (Iic y).indicator K t
  have hJ (y : ℝ) : IntervalIntegrable (J y) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1
      (hK.intervalIntegrable (μ := volume) a b)).indicator measurableSet_Iic
  have split (t : ℝ) :
      ((∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) - T t) * K t =
        (∑ y ∈ Y, J y t) - T t * K t := by
    rw [sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : t ≤ y <;> simp [J, Set.indicator, h]
  change (∫ t in a..b, ((∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) - T t) * K t) = _
  simp_rw [split]
  have isum : IntervalIntegrable (fun t => ∑ y ∈ Y, J y t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    exact integrable_finsetSum Y fun y _ => (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hJ y)
  have iTK : IntervalIntegrable (fun t => T t * K t) volume a b := (cT.mul hK).intervalIntegrable ..
  rw [intervalIntegral.integral_sub isum iTK,intervalIntegral.integral_finsetSum (fun y _ => hJ y)]
  have hj (y : ℝ) (hy : y ∈ Y) : (∫ t in a..b, J y t) = U y - U a := by
    rw [show (∫ t in a..b, J y t) = ∫ t in a..y, K t from
      intervalIntegral.integral_indicator (hY y hy)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hK.intervalIntegrable ..)
  rw [Finset.sum_congr rfl hj, Finset.sum_sub_distrib]
  have Tb : T b = 0 := by simp [T]
  have Ta : T a = Y.card := mass
  simp only [Tb,Ta,zero_mul,zero_sub,neg_mul,intervalIntegral.integral_neg] at parts
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp_rw [mul_comm (ρ _) (U _)] at parts
  linarith

/-- At positive height the logarithmic potential has a smooth real kernel. -/
theorem hasDerivAt_lower_log_norm (x h t : ℝ) (hh : 0 < h) :
    HasDerivAt (fun v : ℝ => Real.log ‖((x-v : ℝ) : ℂ) - (h : ℂ)*Complex.I‖)
      ((t-x)/((x-t)^2+h^2)) t := by
  have pos (v : ℝ) : 0 < (x-v)^2+h^2 := by positivity
  have form (v : ℝ) : Real.log ‖((x-v : ℝ) : ℂ) - (h : ℂ)*Complex.I‖ =
      Real.log ((x-v)^2+h^2)/2 := by
    rw [Complex.norm_def,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_I_re,Complex.mul_I_im,neg_zero,sub_zero,zero_sub,neg_mul_neg]
    simpa only [sq] using Real.log_sqrt (pos v).le
  simp_rw [form]
  have d := (((hasDerivAt_const t x).sub (hasDerivAt_id t)).pow 2).add_const (h^2)
  apply ((d.log (pos t).ne').div_const 2).congr_deriv
  change ((2:ℝ)*(x-t)^1*(0-1)/((x-t)^2+h^2))/2 = (t-x)/((x-t)^2+h^2)
  ring
end MomentSearch

private theorem triangle_log_continuous (B : ℝ → ℂ)
    (hB : ContinuousOn B (Set.Icc 0 2))
    (hsector : ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re) :
    ContinuousOn (fun t => Complex.log (1 + Complex.exp (-(B t)))) (Set.Icc 0 2) := by
  let s := Real.sqrt 3
  have hs : 0 < s := by dsimp [s]; positivity
  have heB : ContinuousOn (fun t => (1 : ℂ) + Complex.exp (-(B t))) (Set.Icc 0 2) :=
    continuousOn_const.add (Complex.continuous_exp.comp_continuousOn hB.neg)
  have hpositive (t : ℝ) (ht : t ∈ Set.Icc 0 2) :
      0 < (1 + Complex.exp (-(B t))).re := by
    have hr0 : 0 ≤ (B t).re := (mul_nonneg hs.le (abs_nonneg _)).trans (hsector t ht)
    by_cases hz : 0 < (B t).re
    · have hq : Real.exp (-(B t).re) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hc := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (B t).im)
        (Real.exp_pos (-(B t).re)).le
      simp only [Complex.add_re, Complex.one_re, Complex.exp_re, Complex.neg_re,
        Complex.neg_im, Real.cos_neg]
      linarith
    · have hr : (B t).re = 0 := le_antisymm (le_of_not_gt hz) hr0
      have hi : (B t).im = 0 := abs_eq_zero.mp (le_antisymm
        (nonpos_of_mul_nonpos_right (hr ▸ hsector t ht) hs) (abs_nonneg _))
      simp only [Complex.add_re, Complex.one_re, Complex.exp_re, Complex.neg_re,
        Complex.neg_im, hr, hi, neg_zero, Real.exp_zero, Real.cos_zero, mul_one]
      norm_num
  intro t ht
  have h : ContinuousAt Complex.log (1 + Complex.exp (-(B t))) :=
    continuousAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl (hpositive t ht)))
  exact h.comp_continuousWithinAt (f := fun t => 1 + Complex.exp (-(B t))) (heB t ht)


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

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let E : ℝ → ℝ → ℝ := fun x h => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) /
        ((x : ℂ) - (h : ℂ)*Complex.I - Z t)).im / Real.pi
    let L : ℝ → ℝ → ℝ := fun v h => Real.log ‖(v : ℂ) - (h : ℂ)*Complex.I‖
    let P : ℝ → ℝ → ℝ := fun x h => (∫ t in (-r)..r,
      h / ((x-t)^2+h^2) * Real.log (2*|f t|)) / Real.pi
    IntervalIntegrable (fun t : ℝ => Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s))
      MeasureTheory.volume 0 2 ∧
    ∀ Y : Finset ℝ, Y.card = N-k → (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) →
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) →
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∉ Y → z ≠ r → z ≠ -r →
        ∀ h : ℝ, 0 < h →
          (∑ y ∈ Y, L (z-y) h) - (∫ t in (-1 : ℝ)..1, L (z-t) h * ρ t) =
            P z h + E z h + E (-z) h := by 
  classical
  intro r ρ f s Z B E L P
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have cf : Continuous ρ := by dsimp [ρ]; fun_prop
  let F := fun u : ℝ => ∫ t in (-r)..u, ρ t
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
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have zeroOutside (z : ℝ) (hz : z ∉ Ioo (-r) r) : ρ z = 0 := by
    have hh : r^2-z^2 ≤ 0 := by
      by_cases hl : -r < z
      · have hzr : r ≤ z := le_of_not_gt (fun h => hz ⟨hl,h⟩)
        nlinarith [sq_le_sq' (by linarith) hzr]
      · have hzr := le_of_not_gt hl
        nlinarith [sq_le_sq' (a := r) (b := -z) (by linarith) (by linarith)]
    simp [ρ,Real.sqrt_eq_zero_of_nonpos hh]
  obtain ⟨d,hB,_,_,_,_,hsec⟩ := MomentSearch.rakhmanov_triangle_phase_geometry N k hk hkN
  change ContinuousOn B (Icc 0 2) at hB
  change ∀ t ∈ Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re at hsec
  constructor
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact (triangle_log_continuous B hB hsec).mul continuousOn_const
  intro Y hc hi hz x _ _ _ _ h hh
  let U := fun t : ℝ => L (x-t) h
  let K := fun t : ℝ => (t-x)/((x-t)^2+h^2)
  have dU (t : ℝ) : HasDerivAt U (K t) t := MomentSearch.hasDerivAt_lower_log_norm x h t hh
  have cU : Continuous U := continuous_iff_continuousAt.mpr fun t => (dU t).continuousAt
  have cK : Continuous K := by exact (continuous_id.sub continuous_const).div (by fun_prop) (fun t => (show 0 < (x-t)^2+h^2 by positivity).ne')
  have mass : (∫ u in (-r)..r, ρ u) = Y.card := by
    rw [hc,Nat.cast_sub hkN.le]; exact htot
  have parts := MomentSearch.quantile_tail_integration_by_parts (-r) r (by linarith) Y
    (fun y hy => Ioo_subset_Icc_self (hi y hy)) ρ U K cf cK dU mass
  have trace := MomentSearch.rakhmanov_triangle_logarithm_trace N k hk hkN Y hc hi hz x h hh
  change (∫ t in (-r)..r, ((∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) -
    (∫ u in t..r, ρ u)) * K t) = P x h + E x h + E (-x) h at trace
  let H := fun t => U t * ρ t
  have cH : Continuous H := cU.mul cf
  have left : (∫ t in (-1:ℝ)..(-r), H t) = 0 := by
    have eqn : EqOn H (fun _ => 0) (uIcc (-1) (-r)) := by
      rw [uIcc_of_le (by linarith)]; intro t ht
      simp [H,zeroOutside t (fun h => (not_lt_of_ge ht.2) h.1)]
    simpa using intervalIntegral.integral_congr (μ := volume) eqn
  have right : (∫ t in r..1, H t) = 0 := by
    have eqn : EqOn H (fun _ => 0) (uIcc r 1) := by
      rw [uIcc_of_le hr1]; intro t ht
      simp [H,zeroOutside t (fun h => (not_lt_of_ge ht.1) h.2)]
    simpa using intervalIntegral.integral_congr (μ := volume) eqn
  have cut := intervalIntegral.integral_add_adjacent_intervals (cH.intervalIntegrable (μ := volume) (-1) (-r)) (cH.intervalIntegrable (-r) r)
  have cut' := intervalIntegral.integral_add_adjacent_intervals (cH.intervalIntegrable (μ := volume) (-1) r) (cH.intervalIntegrable r 1)
  rw [left,zero_add] at cut
  rw [right,add_zero] at cut'
  change (∑ y ∈ Y, U y) - (∫ t in (-1:ℝ)..1, H t) = _
  rw [← cut',← cut]
  exact parts.symm.trans trace
