-- Prove2me | solution 1 for MomentSearch.rakhmanov_quantile_real_regularization
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:09:45.026077+00:00
-- url     : https://prove2.me/submissions/548cc105-fae8-455b-b58d-f593c20b8f56

import Mathlib
open Set

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

open Filter MeasureTheory
open scoped Topology

private theorem potentialContinuous {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : Function.support ρ ⊆ Ioo (-1:ℝ) 1) :
    Continuous (fun z : ℝ => ∫ t in (-1:ℝ)..1, Real.log (1/|z-t|) * ρ t) := by
  have hcompact : HasCompactSupport ρ :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal (hs.trans Ioo_subset_Icc_self) isClosed_Icc)
  have hloc : LocallyIntegrable (fun x : ℝ => -Real.log x) volume := by
    intro x
    refine ⟨Icc (x-1) (x+1),Icc_mem_nhds (by linarith) (by linarith),?_⟩
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : x-1 ≤ x+1)).mp
      (intervalIntegral.intervalIntegrable_log'.neg)
  have hconv := hcompact.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hc hloc
  apply hconv.congr
  intro z
  rw [MeasureTheory.convolution_def, intervalIntegral.integral_eq_integral_of_support_subset]
  · apply integral_congr_ae
    filter_upwards with t
    simp [one_div,Real.log_inv,Real.log_abs,mul_comm]
  · intro t ht
    have hh : ρ t ≠ 0 := by intro h; exact ht (by simp [h])
    exact ⟨(hs hh).1,(hs hh).2.le⟩

private theorem regularQuotient (Y : Finset ℝ) (f : ℝ → ℝ) (cf : Continuous f)
    (roots : ∀ z ∈ Icc (-1:ℝ) 1, z ∈ Y ↔ f z = 0)
    (simple : ∀ y ∈ Y, f y = 0 ∧ HasDerivAt f (deriv f y) y ∧ deriv f y ≠ 0)
    (below : ∀ y ∈ Y, y < 1) (one : f 1 = 1) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc (-1:ℝ) 1) ∧
      ∀ z ∈ Icc (-1:ℝ) 1, 0 < g z ∧ (∏ y ∈ Y, (z-y)) = g z * f z := by
  classical
  let P := fun z => ∏ y ∈ Y, (z-y)
  let Q := fun y z => ∏ u ∈ Y.erase y, (z-u)
  let g := fun z => if z ∈ Y then Q z z / deriv f z else P z / f z
  have cp : Continuous P := by dsimp [P]; fun_prop
  have cq (y : ℝ) : Continuous (Q y) := by dsimp [Q]; fun_prop
  have prod (y : ℝ) (hy : y ∈ Y) (z : ℝ) : Q y z * (z-y) = P z :=
    Y.prod_erase_mul (fun t => z-t) hy
  have cg : ContinuousOn g (Icc (-1:ℝ) 1) := by
    intro y hy
    by_cases h : y ∈ Y
    · obtain ⟨hz,hd,hn⟩ := simple y h
      let D := Function.update (fun z => (f z-f y)/(z-y)) y (deriv f y)
      have cd : ContinuousAt D y := hd.continuousAt_div
      have hD : D y ≠ 0 := by simpa [D] using hn
      apply ContinuousAt.continuousWithinAt
      apply ((cq y).continuousAt.div cd hD).congr_of_eventuallyEq
      have hnb := (Y.erase y).finite_toSet.isClosed.isOpen_compl.mem_nhds
        (show y ∈ (↑(Y.erase y) : Set ℝ)ᶜ by simp)
      filter_upwards [hnb] with z hze
      by_cases e : z = y
      · subst z; simp [g,h,D]
      · have hnot : z ∉ Y := fun hY => hze (Finset.mem_erase.mpr ⟨e,hY⟩)
        simp only [g,if_neg hnot,Pi.div_apply,D,Function.update_of_ne e,hz,sub_zero,← prod y h z]
        rw [div_div_eq_mul_div]
    · have hn : f y ≠ 0 := fun he => h ((roots y hy).mpr he)
      apply ContinuousAt.continuousWithinAt
      apply (cp.continuousAt.div cf.continuousAt hn).congr_of_eventuallyEq
      filter_upwards [Y.finite_toSet.isClosed.isOpen_compl.mem_nhds h] with z hz
      simp [g,show z ∉ Y from hz]
  have nonzero (z : ℝ) (hz : z ∈ Icc (-1:ℝ) 1) : g z ≠ 0 := by
    by_cases h : z ∈ Y
    · simp only [g,if_pos h]
      exact div_ne_zero (Finset.prod_ne_zero_iff.mpr fun t ht =>
        sub_ne_zero.mpr (Finset.mem_erase.mp ht).1.symm) (simple z h).2.2
    · simp only [g,if_neg h]
      exact div_ne_zero (Finset.prod_ne_zero_iff.mpr fun t ht =>
        sub_ne_zero.mpr (fun e => h (e ▸ ht))) (fun he => h ((roots z hz).mpr he))
  have g1 : 0 < g 1 := by
    have h1 : (1:ℝ) ∉ Y := fun h => lt_irrefl _ (below 1 h)
    simpa [g,h1,one,P] using Finset.prod_pos (s := Y) (fun y hy => sub_pos.mpr (below y hy))
  refine ⟨g,cg,fun z hz => ⟨?_,?_⟩⟩
  · by_contra! hn
    obtain ⟨v,hv,he⟩ := intermediate_value_Icc hz.2 (cg.mono (Icc_subset_Icc_left hz.1))
      (show (0:ℝ) ∈ Icc (g z) (g 1) from ⟨hn,g1.le⟩)
    exact nonzero v ⟨hz.1.trans hv.1,hv.2⟩ he
  · by_cases h : z ∈ Y
    · rw [(simple z h).1,mul_zero]
      exact Finset.prod_eq_zero h (sub_self z)
    · change P z = _; simp [g,h,div_mul_cancel₀ _ (show f z ≠ 0 from fun he => h ((roots z hz).mpr he))]

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    ContinuousOn V (Set.Icc (-1 : ℝ) 1) ∧
    ∃ Y : Finset ℝ, Y.card = N-k ∧ (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) ∧
      ∃ g : ℝ → ℝ, ContinuousOn g (Set.Icc (-1 : ℝ) 1) ∧
        ∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < g z ∧
          (∏ y ∈ Y, (z-y)) = g z * f z := by 
  classical
  intro r ρ f V
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
  have hs : Function.support ρ ⊆ Ioo (-r) r := fun z hz => by
    by_contra hh; exact hz (zeroOutside z hh)
  refine ⟨(potentialContinuous cf (hs.trans (Ioo_subset_Ioo (by linarith) hr1))).continuousOn,?_⟩
  let T := fun z : ℝ => ∫ u in z..1, ρ u
  have dt (z : ℝ) : HasDerivAt T (-ρ z) z :=
    intervalIntegral.integral_hasDerivAt_left (cf.intervalIntegrable z 1)
      cf.stronglyMeasurable.stronglyMeasurableAtFilter cf.continuousAt
  have ct : Continuous T := continuous_iff_continuousAt.mpr (fun z => (dt z).continuousAt)
  have tr : T r = 0 := htail
  have tl : T (-r) = m := by change F 1 = _; linarith [inc r 1]
  have pos (y : ℝ) (hy : y ∈ Ioo (-r) r) : 0 < ρ y := by
    have hv : 0 < r^2-y^2 := by nlinarith [mul_pos (sub_pos.mpr hy.2) (show 0<r+y by linarith [hy.1])]
    dsimp [ρ]; exact mul_pos (by positivity) (Real.arctan_pos.mpr (by positivity))
  have strict : StrictAntiOn T (Icc (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..) ct.continuousOn
    intro z hz
    rw [interior_Icc] at hz
    rw [(dt z).deriv]
    exact neg_neg_of_pos (pos _ hz)
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
  have level (i : Fin m) : ∃ y ∈ Ioo (-r) r, T y = (i.val:ℝ)+1/2 := by
    have hi : (i.val:ℝ) < (m:ℝ) := by exact_mod_cast i.isLt
    have hi' : (i.val:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast i.isLt
    obtain ⟨y,hy,he⟩ := intermediate_value_Icc' (show -r ≤ r by linarith) ct.continuousOn
      (show (i.val:ℝ)+1/2 ∈ Icc (T r) (T (-r)) by rw [tr,tl]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i.val])
    exact ⟨y,⟨lt_of_le_of_ne hy.1 (by intro e; rw [← e,tl] at he; linarith),
      lt_of_le_of_ne hy.2 (by intro e; rw [e,tr] at he; linarith [Nat.cast_nonneg (α := ℝ) i.val])⟩,he⟩
  choose y hy hlevel using level
  have inj : Function.Injective y := by
    intro i j he
    apply Fin.ext
    exact_mod_cast (show (i.val:ℝ) = j.val by linarith [hlevel i,hlevel j,congrArg T he])
  let Y := Finset.univ.image y
  have nodes (z : ℝ) : z ∈ Y ↔ ∃ i, y i = z := by simp [Y]
  have inside (z : ℝ) (hz : z ∈ Y) : z ∈ Ioo (-r) r := by
    obtain ⟨i,rfl⟩ := (nodes z).mp hz; exact hy i
  have root (z : ℝ) : z ∈ Y ↔ f z = 0 := by
    change _ ↔ Real.cos (Real.pi * T z) = 0
    rw [Real.cos_eq_zero_iff]
    constructor
    · intro h
      obtain ⟨i,rfl⟩ := (nodes z).mp h
      exact ⟨i.val,by push_cast; rw [hlevel]; ring⟩
    · rintro ⟨j,hj⟩
      have hv : T z = (j:ℝ)+1/2 := by
        apply mul_left_cancel₀ Real.pi_ne_zero
        linarith only [hj]
      have half_ne (n : ℕ) : (n:ℝ) ≠ (j:ℝ)+1/2 := by
        intro h
        have he : 2*(n:ℤ)=2*j+1 := by exact_mod_cast (show 2*(n:ℝ)=2*(j:ℝ)+1 by linarith)
        omega
      have hz : z ∈ Ioo (-r) r := by
        by_contra h
        rcases outside _ h with e | e
        · exact half_ne 0 (by simpa [e] using hv)
        · exact half_ne m (e ▸ hv)
      have hzr := strict ⟨hz.1.le,hz.2.le⟩ ⟨by linarith,le_rfl⟩ hz.2
      have hzl := strict ⟨le_rfl,by linarith⟩ ⟨hz.1.le,hz.2.le⟩ hz.1
      rw [tr,hv] at hzr
      rw [tl,hv] at hzl
      have hjp : 0 ≤ j := by exact_mod_cast (show (-1:ℝ) < j by linarith)
      have hjm : j < (m:ℤ) := by exact_mod_cast (show (j:ℝ) < m by linarith)
      let i : Fin m := ⟨j.toNat,by omega⟩
      apply (nodes z).mpr
      refine ⟨i,strict.injOn (Ioo_subset_Icc_self (hy i)) (Ioo_subset_Icc_self hz) ?_⟩
      rw [hlevel,hv]
      simp [i,← Int.cast_natCast (R := ℝ) j.toNat,Int.toNat_of_nonneg hjp]
  have df (z : ℝ) := ((dt z).const_mul Real.pi).cos
  refine ⟨Y,by simp [Y,Finset.card_image_of_injective _ inj,m],inside,fun z _ => root z,?_⟩
  apply regularQuotient Y f (continuous_iff_continuousAt.mpr fun z => (df z).continuousAt)
    (fun z _ => root z)
  · intro z hz
    have hf := (root z).mp hz
    have dh : HasDerivAt f _ z := df z
    have hs := Real.cos_eq_zero_iff_sin_eq.mp hf
    refine ⟨hf, dh.deriv ▸ dh, ?_⟩
    rw [dh.deriv]
    change -Real.sin (Real.pi*T z) * (Real.pi * -ρ z) ≠ 0
    apply mul_ne_zero (neg_ne_zero.mpr ?_) (mul_ne_zero Real.pi_ne_zero (neg_ne_zero.mpr (pos z (inside z hz)).ne'))
    rcases hs with h | h <;> change Real.sin (Real.pi*T z) = _ at h <;> rw [h] <;> norm_num
  · intro z hz; exact (inside z hz).2.trans_le hr1
  · simp [f]
