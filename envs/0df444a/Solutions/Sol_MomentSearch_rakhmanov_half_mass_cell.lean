-- Prove2me | solution 1 for MomentSearch.rakhmanov_half_mass_cell
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:48:30.89901+00:00
-- url     : https://prove2.me/submissions/5fe6cc84-3921-4d2b-94d3-eed4311c55b9

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

private theorem profileConcave {r c : ℝ} (hc : 0 ≤ c) :
    ConcaveOn ℝ (Icc (-r) r) (fun z => Real.arctan (c * Real.sqrt (r^2-z^2))) := by
  have hat : ConcaveOn ℝ (Ici 0) Real.arctan := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Ici _) Real.continuous_arctan.continuousOn
      Real.differentiable_arctan.differentiableOn
    rw [interior_Ici, Real.deriv_arctan]
    intro u hu v hv huv
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    exact le_of_lt hu
  have hbase : ConcaveOn ℝ (Icc (-r) r) (fun z => r^2-z^2) :=
    (concaveOn_const _ (convex_Icc ..)).sub
      ((even_two.convexOn_pow (𝕜 := ℝ)).subset (subset_univ _) (convex_Icc ..))
  have hs : ConcaveOn ℝ (Icc (-r) r) (fun z => Real.sqrt (r^2-z^2)) := by
    refine ⟨convex_Icc .., ?_⟩
    intro x hx y hy a b ha hb hab
    have pos (u : ℝ) (hu : u ∈ Icc (-r) r) : 0 ≤ r^2-u^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ r+u by linarith [hu.1])]
    exact (Real.strictConcaveOn_sqrt.concaveOn.2 (pos x hx) (pos y hy) ha hb hab).trans
      (Real.sqrt_le_sqrt (hbase.2 hx hy ha hb hab))
  have hsc : ConcaveOn ℝ (Icc (-r) r) (fun z => c * Real.sqrt (r^2-z^2)) := hs.smul hc
  refine ⟨convex_Icc .., ?_⟩
  intro x hx y hy a b ha hb hab
  exact (hat.2 (show 0 ≤ c * Real.sqrt (r^2-x^2) by positivity)
    (show 0 ≤ c * Real.sqrt (r^2-y^2) by positivity) ha hb hab).trans
    (Real.arctan_strictMono.monotone (hsc.2 hx hy ha hb hab))

private theorem rightPeak {f : ℝ → ℝ} {a b y p : ℝ}
    (hf : Continuous f) (hn : ∀ t, 0 ≤ f t) (hc : ConcaveOn ℝ (Icc a b) f)
    (hy : y ∈ Icc a b) (hp : p ∈ Icc a b) (hyp : y ≤ p)
    (hypos : 0 < f y) (hm : (∫ t in a..y, f t) = ∫ t in y..b, f t) :
    f p ≤ 2 * f y := by
  by_contra! h
  have hpy : f y < f p := by linarith
  have hay : a ≤ y := hy.1
  have hab : a ≤ b := hay.trans hy.2
  have hleft : (∫ t in a..y, f t) ≤ (y-a)*f y := by
    have hle := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hay
      (hf.intervalIntegrable a y) (continuous_const.intervalIntegrable a y)
      (g := fun _ => f y) (fun t ht => by
        by_contra! hh
        have hh' := hc.min_le_of_mem_Icc (show t ∈ Icc a b from ⟨ht.1,ht.2.trans hy.2⟩)
          hp (show y ∈ Icc t p from ⟨ht.2,hyp⟩)
        exact (not_lt_of_ge hh') (lt_min hh hpy))
    simpa using hle
  have hright : (p-y)*f y ≤ ∫ t in y..p, f t := by
    have hle := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hyp
      (continuous_const.intervalIntegrable y p) (hf.intervalIntegrable y p)
      (f := fun _ => f y) (fun t ht => by
        simpa [min_eq_left hpy.le] using hc.min_le_of_mem_Icc hy hp ht)
    simpa using hle
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable y p) (hf.intervalIntegrable p b) (μ := MeasureTheory.volume)
  have hpb := intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) hp.2 hn
  have hlen : p-y ≤ y-a := (mul_le_mul_iff_left₀ hypos).mp (by linarith)
  have hv : 2*y-p ∈ Icc a b := ⟨by linarith, by linarith [hy.2]⟩
  have hj := hc.2 hv hp (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show 1/2*(2*y-p)+1/2*p=y by ring] at hj
  linarith [hn (2*y-p)]

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    ∀ x ∈ Set.Ioo (-r) r, ∃ a b y p : ℝ, ∃ m : ℤ,
      y ∈ Set.Ioo (-r) r ∧ y ∈ Set.Icc a b ∧ x ∈ Set.Icc a b ∧
      (∫ t in y..1, ρ t) = (m : ℝ) + 1/2 ∧
      (∫ t in a..y, ρ t) = 1/2 ∧ (∫ t in y..b, ρ t) = 1/2 ∧
      ConcaveOn ℝ (Set.Icc a b) ρ ∧
      (∀ z ∈ Set.Icc a b, ρ z ≤ ρ p) ∧ ρ p ≤ 2 * ρ y := by
  intro r ρ x hx
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have cf : Continuous ρ := by dsimp [ρ]; fun_prop
  have nn (u : ℝ) : 0 ≤ ρ u := by
    dsimp [ρ]; exact mul_nonneg (by positivity) (Real.arctan_nonneg.mpr (by positivity))
  have conc : ConcaveOn ℝ (Icc (-r) r) ρ :=
    (profileConcave (r := r) (show 0 ≤ (N : ℝ)/k by positivity)).smul (by positivity)
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
  let j : ℤ := min ⌊F x⌋ ((N:ℤ)-k-1)
  have hfx0 : 0 ≤ F x := by linarith [mono hx.1.le]
  have hfx1 : F x ≤ (N:ℝ)-k := by linarith [mono hx.2.le]
  have hj0 : 0 ≤ j := le_min (Int.floor_nonneg.mpr hfx0) (by omega)
  have hjN : (j:ℝ)+1 ≤ (N:ℝ)-k := by
    exact_mod_cast (show j+1 ≤ (N:ℤ)-k by dsimp [j]; omega)
  have hfloor : j ≤ ⌊F x⌋ := min_le_left ..
  have hjx : (j:ℝ) ≤ F x := (by exact_mod_cast hfloor : (j:ℝ) ≤ (⌊F x⌋:ℤ)).trans (Int.floor_le _)
  have hxj : F x ≤ (j:ℝ)+1 := by
    dsimp [j]
    rw [Int.cast_min]
    rcases le_total (⌊F x⌋:ℝ) (((N:ℤ)-k-1 : ℤ):ℝ) with h | h
    · rw [min_eq_left h]; exact (Int.lt_floor_add_one _).le
    · rw [min_eq_right h]; push_cast; linarith
  obtain ⟨a,ha,hFa⟩ := intermediate_value_Icc hx.1.le cont.continuousOn
    (show (j:ℝ) ∈ Icc (F (-r)) (F x) from ⟨h0 ▸ (by exact_mod_cast hj0),hjx⟩)
  obtain ⟨b,hb,hFb⟩ := intermediate_value_Icc hx.2.le cont.continuousOn
    (show (j:ℝ)+1 ∈ Icc (F x) (F r) from ⟨hxj,htot ▸ hjN⟩)
  obtain ⟨y,hy,hFy⟩ := intermediate_value_Icc (ha.2.trans hb.1) cont.continuousOn
    (show (j:ℝ)+1/2 ∈ Icc (F a) (F b) from ⟨by linarith,by linarith⟩)
  have hya : a < y := lt_of_le_of_ne hy.1 (by intro e; rw [e] at hFa; linarith)
  have hyb : y < b := lt_of_le_of_ne hy.2 (by intro e; rw [e] at hFy; linarith)
  have hyi : y ∈ Ioo (-r) r := ⟨ha.1.trans_lt hya,hyb.trans_le hb.2⟩
  have hyl : (∫ t in a..y, ρ t) = 1/2 := by linarith [inc a y]
  have hyr : (∫ t in y..b, ρ t) = 1/2 := by linarith [inc y b]
  have hcc := conc.subset (Icc_subset_Icc ha.1 hb.2) (convex_Icc a b)
  obtain ⟨p,hp,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨y,hy⟩ cf.continuousOn
  refine ⟨a,b,y,p,(N:ℤ)-k-j-1,hyi,hy,⟨ha.2,hb.1⟩,?_,hyl,hyr,hcc,hmax,?_⟩
  · push_cast
    linarith [inc y 1,inc r 1]
  · have hpos : 0 < ρ y := by
      have hv : 0 < r^2-y^2 := by nlinarith [mul_pos (sub_pos.mpr hyi.2) (show 0<r+y by linarith [hyi.1])]
      dsimp [ρ]
      exact mul_pos (by positivity) (Real.arctan_pos.mpr (by positivity))
    rcases le_total y p with h | h
    · exact rightPeak cf nn hcc hy hp h hpos (hyl.trans hyr.symm)
    · have even (u : ℝ) : ρ (-u) = ρ u := by simp [ρ]
      have mirror {t : ℝ} (ht : t ∈ Icc (-b) (-a)) : -t ∈ Icc a b :=
        ⟨by linarith [ht.2],by linarith [ht.1]⟩
      have hrev : ConcaveOn ℝ (Icc (-b) (-a)) ρ := by
        refine ⟨convex_Icc .., ?_⟩
        intro u hu v hv c d hc hd hcd
        have hh := hcc.2 (mirror hu) (mirror hv) hc hd hcd
        simp only [smul_eq_mul, mul_neg, ← neg_add, even] at hh
        exact hh
      have rev (u v : ℝ) : (∫ t in (-v)..(-u), ρ t) = ∫ t in u..v, ρ t := by
        simpa only [even] using (intervalIntegral.integral_comp_neg (a := u) (b := v) ρ).symm
      have hh := rightPeak cf nn hrev
        (show -y ∈ Icc (-b) (-a) from ⟨neg_le_neg hy.2,neg_le_neg hy.1⟩)
        (show -p ∈ Icc (-b) (-a) from ⟨neg_le_neg hp.2,neg_le_neg hp.1⟩)
        (neg_le_neg h) (by simpa only [even] using hpos)
        (by rw [rev,rev,hyl,hyr])
      simpa only [even] using hh
