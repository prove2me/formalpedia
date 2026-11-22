-- Prove2me | solution 1 for MartOT.Shadow.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:09:38.463965+00:00
-- url     : https://prove2.me/submissions/bc07682c-4779-40cd-b6b3-33fae3513e6d

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

section MartOTShadowHelpers

/-! ### Section 1: Convex functions on `ℝ` and their right derivatives -/

private noncomputable def rderiv (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin w (Ioi x) x

private lemma convexOn_continuous {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) : Continuous w :=
  continuousOn_univ.mp (hw.continuousOn isOpen_univ)

private lemma rderiv_hasDerivWithinAt {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) (x : ℝ) :
    HasDerivWithinAt w (rderiv w x) (Ioi x) x :=
  hw.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

private lemma rderiv_mono {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) : Monotone (rderiv w) := by
  intro x y hxy
  exact hw.monotoneOn_rightDeriv (by simp) (by simp) hxy

private lemma rderiv_le_slope {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) {x y : ℝ} (hxy : x < y) :
    rderiv w x ≤ (w y - w x) / (y - x) := by
  have h := hw.rightDeriv_le_slope_of_mem_interior (by simp) trivial hxy
  rwa [slope_def_field] at h

private lemma slope_le_rderiv {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) {x y : ℝ} (hxy : x < y) :
    (w y - w x) / (y - x) ≤ rderiv w y := by
  have h1 := hw.slope_le_leftDeriv_of_mem_interior trivial (by simp) hxy
  have h2 := hw.leftDeriv_le_rightDeriv_of_mem_interior (x := y) (by simp)
  have h := h1.trans h2
  rwa [slope_def_field] at h

private lemma rderiv_mul_sub_le {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) {x y : ℝ} (hxy : x ≤ y) :
    rderiv w x * (y - x) ≤ w y - w x := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  · exact (le_div_iff₀ (sub_pos.mpr hlt)).mp (rderiv_le_slope hw hlt)

private lemma sub_le_rderiv_mul {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) {x y : ℝ} (hxy : x ≤ y) :
    w y - w x ≤ rderiv w y * (y - x) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  · exact (div_le_iff₀ (sub_pos.mpr hlt)).mp (slope_le_rderiv hw hlt)

private lemma rderiv_support_line {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) (x₀ y : ℝ) :
    w x₀ + rderiv w x₀ * (y - x₀) ≤ w y := by
  rcases le_or_gt x₀ y with hle | hlt
  · linarith [rderiv_mul_sub_le hw hle]
  · have h := sub_le_rderiv_mul hw hlt.le
    linarith

private lemma rderiv_continuousWithinAt_Ici {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) (x : ℝ) :
    ContinuousWithinAt (rderiv w) (Ici x) x := by
  have hmono : Monotone (rderiv w) := rderiv_mono hw
  set L := sInf (rderiv w '' Ioi x)
  have hT : Tendsto (rderiv w) (𝓝[>] x) (𝓝 L) := hmono.tendsto_nhdsGT x
  have hxL : rderiv w x ≤ L := by
    apply ge_of_tendsto hT
    filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
    exact hmono hy.le
  have hLx : L ≤ rderiv w x := by
    have hslope : Tendsto (fun z => (w z - w x) / (z - x)) (𝓝[>] x) (𝓝 (rderiv w x)) := by
      have hd := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (rderiv_hasDerivWithinAt hw x)
      exact hd.congr fun z => slope_def_field w x z
    refine ge_of_tendsto hslope ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : x < z)
    have hw_cont : Continuous w := convexOn_continuous hw
    have hslope_y : Tendsto (fun y => (w z - w y) / (z - y)) (𝓝[>] x) (𝓝 ((w z - w x) / (z - x))) := by
      have h1 : Tendsto (fun y => w z - w y) (𝓝[>] x) (𝓝 (w z - w x)) :=
        (tendsto_const_nhds.sub (hw_cont.continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun y => z - y) (𝓝[>] x) (𝓝 (z - x)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      exact h1.div h2 (sub_ne_zero.mpr hz.ne')
    refine le_of_tendsto_of_tendsto hT hslope_y ?_
    filter_upwards [Ioo_mem_nhdsGT hz] with y hy
    exact rderiv_le_slope hw hy.2
  have hEq : L = rderiv w x := le_antisymm hLx hxL
  rw [hEq] at hT
  rw [ContinuousWithinAt, ← Ioi_union_left, nhdsWithin_union, tendsto_sup]
  exact ⟨hT, by simp [tendsto_pure_nhds]⟩

private lemma sub_eq_integral_rderiv {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) {a b : ℝ} (hab : a ≤ b) :
    w b - w a = ∫ t in a..b, rderiv w t := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hmono : Monotone (rderiv w) := rderiv_mono hw
  set I := ∫ t in a..b, rderiv w t
  have hbound : ∀ n : ℕ, 0 < n →
      |(w b - w a) - I| ≤ (rderiv w b - rderiv w a) * (b - a) / n := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    set h : ℝ := (b - a) / n
    have hh_pos : 0 < h := div_pos (sub_pos.mpr hlt) hn_pos
    let t : ℕ → ℝ := fun k => a + k * h
    have ht0 : t 0 = a := by simp [t]
    have htn : t n = b := by
      simp only [t, h]
      field_simp [hn_pos.ne']
      ring
    have ht_step : ∀ k, t (k + 1) - t k = h := by
      intro k
      simp only [t, Nat.cast_add, Nat.cast_one]
      ring
    have ht_le : ∀ k, t k ≤ t (k + 1) := fun k => by linarith [ht_step k]
    -- Lower and upper sums
    set Lsum := ∑ k ∈ Finset.range n, rderiv w (t k) * h
    set Usum := ∑ k ∈ Finset.range n, rderiv w (t (k + 1)) * h
    have hw_lo : Lsum ≤ w b - w a := by
      have htel : ∑ k ∈ Finset.range n, (w (t (k + 1)) - w (t k)) = w b - w a := by
        rw [Finset.sum_range_sub (fun k => w (t k)) n, ht0, htn]
      rw [← htel]
      refine Finset.sum_le_sum fun k _ => ?_
      simpa [ht_step k] using rderiv_mul_sub_le hw (ht_le k)
    have hw_hi : w b - w a ≤ Usum := by
      have htel : ∑ k ∈ Finset.range n, (w (t (k + 1)) - w (t k)) = w b - w a := by
        rw [Finset.sum_range_sub (fun k => w (t k)) n, ht0, htn]
      rw [← htel]
      refine Finset.sum_le_sum fun k _ => ?_
      simpa [ht_step k] using sub_le_rderiv_mul hw (ht_le k)
    have hI_eq : I = ∑ k ∈ Finset.range n, ∫ s in t k..t (k + 1), rderiv w s := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hmono.intervalIntegrable),
        ht0, htn]
    have hI_lo : Lsum ≤ I := by
      rw [hI_eq]
      refine Finset.sum_le_sum fun k _ => ?_
      have hc : rderiv w (t k) * h = ∫ _ in t k..t (k + 1), rderiv w (t k) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, ht_step k, mul_comm]
      rw [hc]
      exact intervalIntegral.integral_mono_on (ht_le k) intervalIntegrable_const
        hmono.intervalIntegrable fun s hs => hmono hs.1
    have hI_hi : I ≤ Usum := by
      rw [hI_eq]
      refine Finset.sum_le_sum fun k _ => ?_
      have hc : rderiv w (t (k + 1)) * h = ∫ _ in t k..t (k + 1), rderiv w (t (k + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, ht_step k, mul_comm]
      rw [hc]
      exact intervalIntegral.integral_mono_on (ht_le k) hmono.intervalIntegrable
        intervalIntegrable_const fun s hs => hmono hs.2
    have hdiff : Usum - Lsum = (rderiv w b - rderiv w a) * (b - a) / n := by
      have h1 : Usum - Lsum = (∑ k ∈ Finset.range n, (rderiv w (t (k + 1)) - rderiv w (t k))) * h := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [h1, Finset.sum_range_sub (fun k => rderiv w (t k)) n, ht0, htn]
      simp only [h]
      ring
    rw [abs_le]
    constructor <;> linarith
  have hzero : |(w b - w a) - I| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    by_contra hpos
    push Not at hpos
    set C := (rderiv w b - rderiv w a) * (b - a)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / |(w b - w a) - I|)
    have hn_pos : 0 < n := by
      by_contra h0
      have h0' : n = 0 := Nat.eq_zero_of_not_pos h0
      subst h0'
      have hC0 : 0 ≤ C := mul_nonneg (sub_nonneg.mpr (hmono hab)) (sub_nonneg.mpr hab)
      have : 0 ≤ C / |(w b - w a) - I| := div_nonneg hC0 hpos.le
      linarith
    have hb := hbound n hn_pos
    have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have hlt' : C < |(w b - w a) - I| * n := by
      have := (div_lt_iff₀ hpos).mp hn
      linarith
    have hle' : |(w b - w a) - I| * n ≤ C := (le_div_iff₀ hn_r).mp hb
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

private lemma rderiv_bounds_and_limits {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w) {m b : ℝ}
    (hTop : Tendsto (fun x => w x - (m * x - b)) atTop (𝓝 0))
    (hBot : Tendsto (fun x => w x - (b - m * x)) atBot (𝓝 0)) :
    (∀ x, -m ≤ rderiv w x ∧ rderiv w x ≤ m) ∧
    Tendsto (rderiv w) atTop (𝓝 m) ∧
    Tendsto (rderiv w) atBot (𝓝 (-m)) := by
  have hmono : Monotone (rderiv w) := rderiv_mono hw
  have hle_m : ∀ x, rderiv w x ≤ m := by
    intro x
    have hslope_top : Tendsto (fun z => (w z - w x) / (z - x)) atTop (𝓝 m) := by
      have hzx : Tendsto (fun z : ℝ => z - x) atTop atTop := by
        simpa [sub_eq_add_neg] using tendsto_id.atTop_add (tendsto_const_nhds (x := -x))
      have h1 : Tendsto (fun z => (w z - (m * z - b)) / (z - x)) atTop (𝓝 0) :=
        hTop.div_atTop hzx
      have h2 : Tendsto (fun z => (m * x - b - w x) / (z - x)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hzx
      have h3 : Tendsto (fun z => m + (w z - (m * z - b)) / (z - x) + (m * x - b - w x) / (z - x))
          atTop (𝓝 (m + 0 + 0)) := (tendsto_const_nhds.add h1).add h2
      rw [add_zero, add_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop x] with z hz
      have hne : z - x ≠ 0 := sub_ne_zero.mpr hz.ne'
      field_simp [hne]
      ring
    refine ge_of_tendsto hslope_top ?_
    filter_upwards [eventually_gt_atTop x] with z hz
    exact rderiv_le_slope hw hz
  have hge_neg_m : ∀ x, -m ≤ rderiv w x := by
    intro x
    have hslope_bot : Tendsto (fun z => (w x - w z) / (x - z)) atBot (𝓝 (-m)) := by
      have hzx : Tendsto (fun z : ℝ => x - z) atBot atTop := by
        have := tendsto_atTop_add_const_left atBot x tendsto_neg_atBot_atTop
        simpa [sub_eq_add_neg] using this
      have h1 : Tendsto (fun z => (w z - (b - m * z)) / (x - z)) atBot (𝓝 0) :=
        hBot.div_atTop hzx
      have h2 : Tendsto (fun z => (w x - (b - m * x)) / (x - z)) atBot (𝓝 0) :=
        tendsto_const_nhds.div_atTop hzx
      have h3 : Tendsto (fun z => -m - (w z - (b - m * z)) / (x - z) + (w x - (b - m * x)) / (x - z))
          atBot (𝓝 (-m - 0 + 0)) := (tendsto_const_nhds.sub h1).add h2
      rw [sub_zero, add_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_lt_atBot x] with z hz
      have hne : x - z ≠ 0 := sub_ne_zero.mpr hz.ne'
      field_simp [hne]
      ring
    refine le_of_tendsto hslope_bot ?_
    filter_upwards [eventually_lt_atBot x] with z hz
    exact slope_le_rderiv hw hz
  have hT_top : Tendsto (rderiv w) atTop (𝓝 m) := by
    have hbdd : BddAbove (range (rderiv w)) := ⟨m, by rintro _ ⟨x, rfl⟩; exact hle_m x⟩
    set L := ⨆ x, rderiv w x
    have hTL : Tendsto (rderiv w) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
    have hLm : L ≤ m := ciSup_le hle_m
    have hmL : m ≤ L := by
      have hslope_top : Tendsto (fun z => (w z - w 0) / z) atTop (𝓝 m) := by
        have h1 : Tendsto (fun z => (w z - (m * z - b)) / z) atTop (𝓝 0) :=
          hTop.div_atTop tendsto_id
        have h2 : Tendsto (fun z => (-b - w 0) / z) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h3 : Tendsto (fun z => m + (w z - (m * z - b)) / z + (-b - w 0) / z)
            atTop (𝓝 (m + 0 + 0)) := (tendsto_const_nhds.add h1).add h2
        rw [add_zero, add_zero] at h3
        refine h3.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        field_simp [hz.ne']
        ring
      refine le_of_tendsto hslope_top ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      have h1 : w z - w 0 ≤ rderiv w z * z := by
        simpa using sub_le_rderiv_mul hw hz.le
      have h2 : rderiv w z ≤ L := le_ciSup hbdd z
      have h3 : (w z - w 0) / z ≤ rderiv w z := (div_le_iff₀ hz).mpr h1
      exact h3.trans h2
    rwa [le_antisymm hLm hmL] at hTL
  have hT_bot : Tendsto (rderiv w) atBot (𝓝 (-m)) := by
    have hbdd : BddBelow (range (rderiv w)) := ⟨-m, by rintro _ ⟨x, rfl⟩; exact hge_neg_m x⟩
    set L := ⨅ x, rderiv w x
    have hTL : Tendsto (rderiv w) atBot (𝓝 L) := tendsto_atBot_ciInf hmono hbdd
    have hmL : -m ≤ L := le_ciInf hge_neg_m
    have hLm : L ≤ -m := by
      have hslope_bot : Tendsto (fun z => (w 0 - w z) / (0 - z)) atBot (𝓝 (-m)) := by
        have hz0 : Tendsto (fun z : ℝ => (0 : ℝ) - z) atBot atTop := by
          simpa using tendsto_neg_atBot_atTop
        have h1 : Tendsto (fun z => (w z - (b - m * z)) / (0 - z)) atBot (𝓝 0) :=
          hBot.div_atTop hz0
        have h2 : Tendsto (fun z => (w 0 - b) / (0 - z)) atBot (𝓝 0) :=
          tendsto_const_nhds.div_atTop hz0
        have h3 : Tendsto (fun z => -m - (w z - (b - m * z)) / (0 - z) + (w 0 - b) / (0 - z))
            atBot (𝓝 (-m - 0 + 0)) := (tendsto_const_nhds.sub h1).add h2
        rw [sub_zero, add_zero] at h3
        refine h3.congr' ?_
        filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
        have hne : (0 : ℝ) - z ≠ 0 := sub_ne_zero.mpr hz.ne'
        field_simp [hne]
        ring
      refine ge_of_tendsto hslope_bot ?_
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with z hz
      have h1 : L ≤ rderiv w z := ciInf_le hbdd z
      have h2 : rderiv w z ≤ (w 0 - w z) / (0 - z) := rderiv_le_slope hw hz
      exact h1.trans h2
    rwa [le_antisymm hLm hmL] at hTL
  exact ⟨fun x => ⟨hge_neg_m x, hle_m x⟩, hT_top, hT_bot⟩

/-! ### Section 2: Potential functions, calls/puts, injectivity, and reconstruction -/

private noncomputable def mass (μ : Measure ℝ) : ℝ := (μ univ).toReal
private noncomputable def bary (μ : Measure ℝ) : ℝ := ∫ y, y ∂μ
private noncomputable def call (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, max (y - x) 0 ∂μ
private noncomputable def put (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, max (x - y) 0 ∂μ

private lemma inM_of_le {μ ν : Measure ℝ} (hν : MartOT.Var.InM ν) (hle : μ ≤ ν) :
    MartOT.Var.InM μ := by
  have : IsFiniteMeasure ν := hν.1
  exact ⟨isFiniteMeasure_of_le ν hle, hν.2.mono_measure hle⟩

private lemma inM_add {μ ν : Measure ℝ} (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) :
    MartOT.Var.InM (μ + ν) := by
  have : IsFiniteMeasure μ := hμ.1
  have : IsFiniteMeasure ν := hν.1
  exact ⟨inferInstance, integrable_add_measure.mpr ⟨hμ.2, hν.2⟩⟩

private lemma integrable_abs_sub {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => |y - x|) μ := by
  have : IsFiniteMeasure μ := hμ.1
  exact (hμ.2.sub (integrable_const x)).abs

private lemma integrable_call {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => max (y - x) 0) μ := by
  have : IsFiniteMeasure μ := hμ.1
  exact (hμ.2.sub (integrable_const x)).sup (integrable_const 0)

private lemma integrable_put {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => max (x - y) 0) μ := by
  have : IsFiniteMeasure μ := hμ.1
  exact ((integrable_const x).sub hμ.2).sup (integrable_const 0)

private lemma call_add_put {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    call μ x + put μ x = MartOT.Var.potential μ x := by
  unfold call put MartOT.Var.potential
  rw [← integral_add (integrable_call hμ x) (integrable_put hμ x)]
  congr 1 with y
  rcases le_or_gt x y with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h), abs_of_nonneg (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h.le), max_eq_left (sub_nonneg.mpr h.le), abs_of_neg (sub_neg.mpr h)]
    ring

private lemma call_sub_put {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    call μ x - put μ x = bary μ - mass μ * x := by
  have : IsFiniteMeasure μ := hμ.1
  unfold call put bary mass
  rw [← integral_sub (integrable_call hμ x) (integrable_put hμ x)]
  have hpt : (fun y : ℝ => max (y - x) 0 - max (x - y) 0) = fun y => y - x := by
    ext y
    rcases le_or_gt x y with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
    · rw [max_eq_right (sub_nonpos.mpr h.le), max_eq_left (sub_nonneg.mpr h.le)]; ring
  rw [hpt, integral_sub hμ.2 (integrable_const x), integral_const, smul_eq_mul, Measure.real_def]

private lemma potential_sub_right_asymp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    MartOT.Var.potential μ x - (mass μ * x - bary μ) = 2 * call μ x := by
  linarith [call_add_put hμ x, call_sub_put hμ x]

private lemma potential_sub_left_asymp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    MartOT.Var.potential μ x - (bary μ - mass μ * x) = 2 * put μ x := by
  linarith [call_add_put hμ x, call_sub_put hμ x]

private lemma call_tendsto_atTop {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (call μ) atTop (𝓝 0) := by
  have : IsFiniteMeasure μ := hμ.1
  have hzero : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) ∂μ := by simp
  rw [hzero]
  refine tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => |y|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (integrable_call hμ x).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self y]) (abs_nonneg y)
  · exact hμ.2.abs
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop y] with x hx
    exact (max_eq_right (sub_nonpos.mpr hx)).symm

private lemma put_tendsto_atBot {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (put μ) atBot (𝓝 0) := by
  have : IsFiniteMeasure μ := hμ.1
  have hzero : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) ∂μ := by simp
  rw [hzero]
  refine tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => |y|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (integrable_put hμ x).aestronglyMeasurable
  · filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [neg_le_abs y]) (abs_nonneg y)
  · exact hμ.2.abs
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot y] with x hx
    exact (max_eq_right (sub_nonpos.mpr hx)).symm

private lemma potential_tendsto_right_asymp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (fun x => MartOT.Var.potential μ x - (mass μ * x - bary μ)) atTop (𝓝 0) := by
  simp_rw [potential_sub_right_asymp hμ]
  simpa using (call_tendsto_atTop hμ).const_mul 2

private lemma potential_tendsto_left_asymp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (fun x => MartOT.Var.potential μ x - (bary μ - mass μ * x)) atBot (𝓝 0) := by
  simp_rw [potential_sub_left_asymp hμ]
  simpa using (put_tendsto_atBot hμ).const_mul 2

private lemma potential_convexOn {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    ConvexOn ℝ univ (MartOT.Var.potential μ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, MartOT.Var.potential]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_abs_sub hμ x).const_mul a) ((integrable_abs_sub hμ y).const_mul b)]
  refine integral_mono (integrable_abs_sub hμ _)
    (((integrable_abs_sub hμ x).const_mul a).add ((integrable_abs_sub hμ y).const_mul b)) fun z => ?_
  have h1 : z - (a * x + b * y) = a * (z - x) + b * (z - y) := by
    calc z - (a * x + b * y) = (a + b) * z - (a * x + b * y) := by rw [hab, one_mul]
      _ = a * (z - x) + b * (z - y) := by ring
  rw [h1]
  calc |a * (z - x) + b * (z - y)| ≤ |a * (z - x)| + |b * (z - y)| := abs_add_le _ _
    _ = a * |z - x| + b * |z - y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

private lemma potential_add {μ ν : Measure ℝ} (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (x : ℝ) :
    MartOT.Var.potential (μ + ν) x = MartOT.Var.potential μ x + MartOT.Var.potential ν x :=
  integral_add_measure (integrable_abs_sub hμ x) (integrable_abs_sub hν x)

private lemma rderiv_potential {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    rderiv (MartOT.Var.potential μ) x = 2 * (μ (Iic x)).toReal - mass μ := by
  have : IsFiniteMeasure μ := hμ.1
  have hconv := potential_convexOn hμ
  have hslope_lim : Tendsto (fun n : ℕ =>
      (MartOT.Var.potential μ (x + 1 / ((n : ℝ) + 1)) - MartOT.Var.potential μ x) /
        (1 / ((n : ℝ) + 1))) atTop (𝓝 (rderiv (MartOT.Var.potential μ) x)) := by
    have hd := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (rderiv_hasDerivWithinAt hconv x)
    have hseq : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝[>] x) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using tendsto_const_nhds.add h1
      · exact Eventually.of_forall fun n => by
          change x < x + 1 / ((n : ℝ) + 1)
          linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
    have hcomp := hd.comp hseq
    refine hcomp.congr fun n => ?_
    simp [slope_def_field]
  let g : ℝ → ℝ := (Iic x).indicator (fun _ => (1 : ℝ)) - (Ioi x).indicator (fun _ => (1 : ℝ))
  have hdom : Tendsto (fun n : ℕ =>
      ∫ y, (|y - (x + 1 / ((n : ℝ) + 1))| - |y - x|) / (1 / ((n : ℝ) + 1)) ∂μ) atTop
      (𝓝 (∫ y, g y ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro n
      exact (((integrable_abs_sub hμ _).sub (integrable_abs_sub hμ x)).div_const _).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun y => ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_one hpos]
      have htri := abs_abs_sub_abs_le_abs_sub (y - (x + 1 / ((n : ℝ) + 1))) (y - x)
      have hsub : (y - (x + 1 / ((n : ℝ) + 1))) - (y - x) = -(1 / ((n : ℝ) + 1)) := by ring
      rw [hsub, abs_neg, abs_of_pos hpos] at htri
      exact htri
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : y ≤ x
      · have hgx : g y = 1 := by
          simp [g, Set.indicator_of_mem (show y ∈ Iic x from hy),
            Set.indicator_of_notMem (show y ∉ Ioi x from not_lt.mpr hy)]
        rw [hgx]
        refine tendsto_const_nhds.congr fun n => ?_
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        rw [abs_of_nonpos (by linarith : y - (x + 1 / ((n : ℝ) + 1)) ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]
        have : -(y - (x + 1 / ((n : ℝ) + 1))) - -(y - x) = 1 / ((n : ℝ) + 1) := by ring
        rw [this, div_self hpos.ne']
      · push Not at hy
        have hgx : g y = -1 := by
          simp [g, Set.indicator_of_notMem (show y ∉ Iic x from not_le.mpr hy),
            Set.indicator_of_mem (show y ∈ Ioi x from hy)]
        rw [hgx]
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / (y - x))
        filter_upwards [eventually_ge_atTop N] with n hn
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hlt : 1 / ((n : ℝ) + 1) < y - x := by
          have hyx : 0 < y - x := sub_pos.mpr hy
          have h1 : 1 / (y - x) < (n : ℝ) + 1 := lt_of_lt_of_le hN (by linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr hn])
          have h2 : 1 < ((n : ℝ) + 1) * (y - x) := (div_lt_iff₀ hyx).mp h1
          exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
        rw [abs_of_pos (by linarith : 0 < y - (x + 1 / ((n : ℝ) + 1))),
          abs_of_pos (sub_pos.mpr hy)]
        have : (y - (x + 1 / ((n : ℝ) + 1))) - (y - x) = -(1 / ((n : ℝ) + 1)) := by ring
        rw [this, neg_div, div_self hpos.ne']
  have heq_seq : (fun n : ℕ =>
      (MartOT.Var.potential μ (x + 1 / ((n : ℝ) + 1)) - MartOT.Var.potential μ x) /
        (1 / ((n : ℝ) + 1))) =
      fun n : ℕ => ∫ y, (|y - (x + 1 / ((n : ℝ) + 1))| - |y - x|) / (1 / ((n : ℝ) + 1)) ∂μ := by
    ext n
    unfold MartOT.Var.potential
    rw [← integral_sub (integrable_abs_sub hμ _) (integrable_abs_sub hμ x), integral_div]
  rw [heq_seq] at hslope_lim
  have hval := tendsto_nhds_unique hslope_lim hdom
  rw [hval]
  have hint1 : Integrable ((Iic x).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator measurableSet_Iic
  have hint2 : Integrable ((Ioi x).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator measurableSet_Ioi
  change ∫ y, ((Iic x).indicator (fun _ => (1 : ℝ)) y - (Ioi x).indicator (fun _ => (1 : ℝ)) y) ∂μ = _
  rw [integral_sub hint1 hint2, integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    Measure.real_def, Measure.real_def]
  have huniv : μ (Iic x) + μ (Ioi x) = μ univ := by
    have hdisj : Disjoint (Iic x) (Ioi x) :=
      Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge (mem_Iic.mp h1) (mem_Ioi.mp h2)
    rw [← measure_union hdisj measurableSet_Ioi, Iic_union_Ioi]
  have huniv_r : (μ (Iic x)).toReal + (μ (Ioi x)).toReal = mass μ := by
    unfold mass
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), huniv]
  linarith

private lemma mass_eq_of_potential_eq {μ₁ μ₂ : Measure ℝ}
    (h₁ : MartOT.Var.InM μ₁) (h₂ : MartOT.Var.InM μ₂)
    (heq : ∀ x, MartOT.Var.potential μ₁ x = MartOT.Var.potential μ₂ x) :
    mass μ₁ = mass μ₂ := by
  have h1 := (rderiv_bounds_and_limits (potential_convexOn h₁)
    (potential_tendsto_right_asymp h₁) (potential_tendsto_left_asymp h₁)).2.1
  have h2 := (rderiv_bounds_and_limits (potential_convexOn h₂)
    (potential_tendsto_right_asymp h₂) (potential_tendsto_left_asymp h₂)).2.1
  have hfun : MartOT.Var.potential μ₁ = MartOT.Var.potential μ₂ := funext heq
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 h2

private lemma eq_of_potential_eq {μ₁ μ₂ : Measure ℝ}
    (h₁ : MartOT.Var.InM μ₁) (h₂ : MartOT.Var.InM μ₂)
    (heq : ∀ x, MartOT.Var.potential μ₁ x = MartOT.Var.potential μ₂ x) :
    μ₁ = μ₂ := by
  have : IsFiniteMeasure μ₁ := h₁.1
  have : IsFiniteMeasure μ₂ := h₂.1
  have hm := mass_eq_of_potential_eq h₁ h₂ heq
  have hfun : MartOT.Var.potential μ₁ = MartOT.Var.potential μ₂ := funext heq
  refine Measure.ext_of_Iic μ₁ μ₂ fun x => ?_
  have hr1 := rderiv_potential h₁ x
  have hr2 := rderiv_potential h₂ x
  rw [hfun] at hr1
  have hreal : (μ₁ (Iic x)).toReal = (μ₂ (Iic x)).toReal := by linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ₁ _) (measure_ne_top μ₂ _)).mp hreal

/-- **Potential-to-Measure Reconstruction**: any convex function `w` with linear asymptotes
`m * x - b` at `+∞` and `b - m * x` at `-∞` (with `m ≥ 0`) is the potential of a measure in `𝓜`. -/
private lemma exists_measure_of_potential {w : ℝ → ℝ} (hw : ConvexOn ℝ univ w)
    {m b : ℝ} (hm : 0 ≤ m)
    (hTop : Tendsto (fun x => w x - (m * x - b)) atTop (𝓝 0))
    (hBot : Tendsto (fun x => w x - (b - m * x)) atBot (𝓝 0)) :
    ∃ γ : Measure ℝ, MartOT.Var.InM γ ∧ mass γ = m ∧ bary γ = b ∧
      ∀ x, MartOT.Var.potential γ x = w x := by
  obtain ⟨hbnd, hD_top, hD_bot⟩ := rderiv_bounds_and_limits hw hTop hBot
  let F : StieltjesFunction ℝ :=
    { toFun := fun x => (rderiv w x + m) / 2
      mono' := fun x y hxy => by linarith [rderiv_mono hw hxy]
      right_continuous' := fun x =>
        ((rderiv_continuousWithinAt_Ici hw x).add continuousWithinAt_const).div_const 2 }
  have hF_bot : Tendsto F atBot (𝓝 0) := by
    have := (hD_bot.add_const m).div_const 2
    simpa [F] using this
  have hF_top : Tendsto F atTop (𝓝 m) := by
    have := (hD_top.add_const m).div_const 2
    have h2m : (m + m) / 2 = m := by ring
    simpa [F, h2m] using this
  let γ : Measure ℝ := F.measure
  have hγ_fin : IsFiniteMeasure γ := F.isFiniteMeasure hF_bot hF_top
  have hγ_univ : γ univ = ENNReal.ofReal m := by
    simpa [γ] using F.measure_univ hF_bot hF_top
  have hγ_mass : mass γ = m := by
    simp [mass, hγ_univ, ENNReal.toReal_ofReal hm]
  have hγ_Iic : ∀ t, γ (Iic t) = ENNReal.ofReal (F t) := fun t => by
    simpa [γ] using F.measure_Iic hF_bot t
  have hγ_Ioi : ∀ t, γ (Ioi t) = ENNReal.ofReal (m - F t) := fun t => by
    simpa [γ] using F.measure_Ioi hF_top t
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => by
    change 0 ≤ (rderiv w t + m) / 2
    linarith [(hbnd t).1]
  have hF_le_m : ∀ t, F t ≤ m := fun t => by
    change (rderiv w t + m) / 2 ≤ m
    linarith [(hbnd t).2]
  -- Compute lintegral of max (y - x) 0 via layercake
  have hcall_lin : ∀ x, ∫⁻ y, ENNReal.ofReal (max (y - x) 0) ∂γ =
      ENNReal.ofReal ((w x - (m * x - b)) / 2) := by
    intro x
    rw [lintegral_eq_lintegral_meas_lt γ (f := fun y : ℝ => max (y - x) 0)
      (Eventually.of_forall fun _ => le_max_right _ _)
      ((measurable_id.sub measurable_const).sup measurable_const).aemeasurable]
    have hmeas_eq : ∀ t ∈ Ioi (0 : ℝ),
        γ {y : ℝ | t < max (y - x) 0} = ENNReal.ofReal (m - F (x + t)) := by
      intro t ht
      have hset : {y : ℝ | t < max (y - x) 0} = Ioi (x + t) := by
        ext y
        simp only [mem_ofPred_eq, mem_Ioi, lt_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith [show (0 : ℝ) < t from ht]
        · intro h
          left; linarith
      rw [hset, hγ_Ioi (x + t)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hmeas_eq]
    have hIoi_union : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1) := by
      ext t
      simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_gt t
        exact ⟨n, ht, by linarith⟩
      · rintro ⟨_, ht, _⟩
        exact ht
    have hmono_sets : Monotone (fun n : ℕ => Ioc (0 : ℝ) ((n : ℝ) + 1)) := fun i j hij =>
      Ioc_subset_Ioc_right (by exact_mod_cast Nat.add_le_add_right hij 1)
    rw [hIoi_union, setLIntegral_iUnion_of_directed
      (fun t => ENNReal.ofReal (m - F (x + t))) hmono_sets.directed_le]
    have htrunc : ∀ n : ℕ,
        ∫⁻ t in Ioc (0 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (m - F (x + t)) =
          ENNReal.ofReal ((w x - (m * x - b)) / 2 -
            (w (x + ((n : ℝ) + 1)) - (m * (x + ((n : ℝ) + 1)) - b)) / 2) := by
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hint_int : IntervalIntegrable (fun t => m - F (x + t)) volume 0 ((n : ℝ) + 1) := by
        have hF_mono : Monotone (fun t => F (x + t)) := fun s t hst => F.mono (by linarith)
        exact intervalIntegrable_const.sub hF_mono.intervalIntegrable
      have hint_set : IntegrableOn (fun t => m - F (x + t)) (Ioc 0 ((n : ℝ) + 1)) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hn).mp hint_int
      rw [← ofReal_integral_eq_lintegral_ofReal hint_set
        (Eventually.of_forall fun t => sub_nonneg.mpr (hF_le_m (x + t)))]
      congr 1
      rw [← intervalIntegral.integral_of_le hn]
      have hsub_val : (∫ t in (0 : ℝ)..((n : ℝ) + 1), (m - F (x + t))) =
          (∫ t in (0 : ℝ)..((n : ℝ) + 1), (m - rderiv w (x + t)) / 2) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        change m - (rderiv w (x + t) + m) / 2 = (m - rderiv w (x + t)) / 2
        ring
      have hmono_x : Monotone (fun t => rderiv w (x + t)) :=
        fun _ _ h => rderiv_mono hw (by linarith)
      rw [hsub_val, intervalIntegral.integral_div,
        intervalIntegral.integral_sub intervalIntegrable_const hmono_x.intervalIntegrable,
        intervalIntegral.integral_const, smul_eq_mul, sub_zero,
        intervalIntegral.integral_comp_add_left (rderiv w) x,
        add_zero, ← sub_eq_integral_rderiv hw (by linarith : x ≤ x + ((n : ℝ) + 1))]
      ring
    simp_rw [htrunc]
    have hlim_r : Tendsto (fun n : ℕ =>
        (w x - (m * x - b)) / 2 - (w (x + ((n : ℝ) + 1)) - (m * (x + ((n : ℝ) + 1)) - b)) / 2)
        atTop (𝓝 ((w x - (m * x - b)) / 2)) := by
      have hx_top : Tendsto (fun n : ℕ => x + ((n : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_left atTop x (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h2 := (hTop.comp hx_top).div_const 2
      simpa using tendsto_const_nhds.sub h2
    have hlim : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((w x - (m * x - b)) / 2 -
          (w (x + ((n : ℝ) + 1)) - (m * (x + ((n : ℝ) + 1)) - b)) / 2))
        atTop (𝓝 (ENNReal.ofReal ((w x - (m * x - b)) / 2))) :=
      ENNReal.tendsto_ofReal hlim_r
    have hmono_seq : Monotone (fun n : ℕ =>
        ENNReal.ofReal ((w x - (m * x - b)) / 2 -
          (w (x + ((n : ℝ) + 1)) - (m * (x + ((n : ℝ) + 1)) - b)) / 2)) := by
      intro i j hij
      dsimp only
      rw [← htrunc i, ← htrunc j]
      exact lintegral_mono_set (hmono_sets hij)
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono_seq) hlim
  -- Compute lintegral of max (x - y) 0 via layercake
  have hput_lin : ∀ x, ∫⁻ y, ENNReal.ofReal (max (x - y) 0) ∂γ =
      ENNReal.ofReal ((w x - (b - m * x)) / 2) := by
    intro x
    rw [lintegral_eq_lintegral_meas_le γ (f := fun y : ℝ => max (x - y) 0)
      (Eventually.of_forall fun _ => le_max_right _ _)
      ((measurable_const.sub measurable_id).sup measurable_const).aemeasurable]
    have hmeas_eq : ∀ t ∈ Ioi (0 : ℝ),
        γ {y : ℝ | t ≤ max (x - y) 0} = ENNReal.ofReal (F (x - t)) := by
      intro t ht
      have hset : {y : ℝ | t ≤ max (x - y) 0} = Iic (x - t) := by
        ext y
        simp only [mem_ofPred_eq, mem_Iic, le_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith [show (0 : ℝ) < t from ht]
        · intro h
          left; linarith
      rw [hset, hγ_Iic (x - t)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hmeas_eq]
    have hIoi_union : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1) := by
      ext t
      simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_gt t
        exact ⟨n, ht, by linarith⟩
      · rintro ⟨_, ht, _⟩
        exact ht
    have hmono_sets : Monotone (fun n : ℕ => Ioc (0 : ℝ) ((n : ℝ) + 1)) := fun i j hij =>
      Ioc_subset_Ioc_right (by exact_mod_cast Nat.add_le_add_right hij 1)
    rw [hIoi_union, setLIntegral_iUnion_of_directed
      (fun t => ENNReal.ofReal (F (x - t))) hmono_sets.directed_le]
    have htrunc : ∀ n : ℕ,
        ∫⁻ t in Ioc (0 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (F (x - t)) =
          ENNReal.ofReal ((w x - (b - m * x)) / 2 -
            (w (x - ((n : ℝ) + 1)) - (b - m * (x - ((n : ℝ) + 1)))) / 2) := by
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hint_int : IntervalIntegrable (fun t => F (x - t)) volume 0 ((n : ℝ) + 1) := by
        have hF_anti : Antitone (fun t => F (x - t)) := fun s t hst => F.mono (by linarith)
        exact hF_anti.intervalIntegrable
      have hint_set : IntegrableOn (fun t => F (x - t)) (Ioc 0 ((n : ℝ) + 1)) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hn).mp hint_int
      rw [← ofReal_integral_eq_lintegral_ofReal hint_set
        (Eventually.of_forall fun t => hF_nonneg (x - t))]
      congr 1
      rw [← intervalIntegral.integral_of_le hn]
      have hsub_val : (∫ t in (0 : ℝ)..((n : ℝ) + 1), F (x - t)) =
          (∫ t in (0 : ℝ)..((n : ℝ) + 1), (rderiv w (x - t) + m) / 2) := rfl
      have hanti_x : Antitone (fun t => rderiv w (x - t)) :=
        fun _ _ h => rderiv_mono hw (by linarith)
      rw [hsub_val, intervalIntegral.integral_div,
        intervalIntegral.integral_add hanti_x.intervalIntegrable intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, sub_zero,
        intervalIntegral.integral_comp_sub_left (rderiv w) x,
        sub_zero, ← sub_eq_integral_rderiv hw (by linarith : x - ((n : ℝ) + 1) ≤ x)]
      ring
    simp_rw [htrunc]
    have hlim_r : Tendsto (fun n : ℕ =>
        (w x - (b - m * x)) / 2 - (w (x - ((n : ℝ) + 1)) - (b - m * (x - ((n : ℝ) + 1)))) / 2)
        atTop (𝓝 ((w x - (b - m * x)) / 2)) := by
      have hx_bot : Tendsto (fun n : ℕ => x - ((n : ℝ) + 1)) atTop atBot := by
        have h1 : Tendsto (fun n : ℕ => -(((n : ℝ) + 1))) atTop atBot :=
          tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop x h1
      have h2 := (hBot.comp hx_bot).div_const 2
      simpa using tendsto_const_nhds.sub h2
    have hlim : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((w x - (b - m * x)) / 2 -
          (w (x - ((n : ℝ) + 1)) - (b - m * (x - ((n : ℝ) + 1)))) / 2))
        atTop (𝓝 (ENNReal.ofReal ((w x - (b - m * x)) / 2))) :=
      ENNReal.tendsto_ofReal hlim_r
    have hmono_seq : Monotone (fun n : ℕ =>
        ENNReal.ofReal ((w x - (b - m * x)) / 2 -
          (w (x - ((n : ℝ) + 1)) - (b - m * (x - ((n : ℝ) + 1)))) / 2)) := by
      intro i j hij
      dsimp only
      rw [← htrunc i, ← htrunc j]
      exact lintegral_mono_set (hmono_sets hij)
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono_seq) hlim
  -- Deduce w(x) ≥ m*x - b and w(x) ≥ b - m*x from convexity and asymptotics
  have hw_ge_right : ∀ x, m * x - b ≤ w x := by
    intro x
    have h1 : ∀ z ≥ x, w z - w x ≤ m * (z - x) := fun z hz => by
      have := sub_le_rderiv_mul hw hz
      have := (hbnd z).2
      nlinarith
    have hlim : Tendsto (fun z => w z - (m * z - b)) atTop (𝓝 0) := hTop
    have hge : 0 ≤ w x - (m * x - b) := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop x] with z hz
      linarith [h1 z hz]
    linarith
  have hw_ge_left : ∀ x, b - m * x ≤ w x := by
    intro x
    have h1 : ∀ z ≤ x, -m * (x - z) ≤ w x - w z := fun z hz => by
      have := rderiv_mul_sub_le hw hz
      have := (hbnd z).1
      nlinarith
    have hlim : Tendsto (fun z => w z - (b - m * z)) atBot (𝓝 0) := hBot
    have hge : 0 ≤ w x - (b - m * x) := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_le_atBot x] with z hz
      linarith [h1 z hz]
    linarith
  -- Deduce Integrable id γ, hence InM γ
  have hγ_int : Integrable (fun y : ℝ => y) γ := by
    refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
    rw [← hasFiniteIntegral_norm_iff,
      hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => norm_nonneg _)]
    have hpt : ∀ y : ℝ, ENNReal.ofReal ‖y‖ =
        ENNReal.ofReal (max (y - 0) 0) + ENNReal.ofReal (max (0 - y) 0) := by
      intro y
      rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
      congr 1
      rw [Real.norm_eq_abs]
      rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h, sub_zero, zero_sub, max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [abs_of_neg h, sub_zero, zero_sub, max_eq_right h.le, max_eq_left (by linarith)]; ring
    simp_rw [hpt]
    have hm_pos : Measurable (fun y : ℝ => ENNReal.ofReal (max (y - 0) 0)) := by fun_prop
    rw [lintegral_add_left hm_pos, hcall_lin 0, hput_lin 0]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have hγ_inM : MartOT.Var.InM γ := ⟨hγ_fin, hγ_int⟩
  have hcall_eq : ∀ x, call γ x = (w x - (m * x - b)) / 2 := by
    intro x
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_call hγ_inM x)
      (Eventually.of_forall fun _ => le_max_right _ _)
    rw [hcall_lin x] at h1
    have hnn1 : 0 ≤ call γ x := integral_nonneg fun _ => le_max_right _ _
    have hnn2 : 0 ≤ (w x - (m * x - b)) / 2 := by linarith [hw_ge_right x]
    exact (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp h1
  have hput_eq : ∀ x, put γ x = (w x - (b - m * x)) / 2 := by
    intro x
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_put hγ_inM x)
      (Eventually.of_forall fun _ => le_max_right _ _)
    rw [hput_lin x] at h1
    have hnn1 : 0 ≤ put γ x := integral_nonneg fun _ => le_max_right _ _
    have hnn2 : 0 ≤ (w x - (b - m * x)) / 2 := by linarith [hw_ge_left x]
    exact (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp h1
  have hγ_bary : bary γ = b := by
    have h := call_sub_put hγ_inM 0
    rw [hcall_eq 0, hput_eq 0] at h
    linarith
  have hγ_pot : ∀ x, MartOT.Var.potential γ x = w x := by
    intro x
    rw [← call_add_put hγ_inM x, hcall_eq x, hput_eq x]
    ring
  exact ⟨γ, hγ_inM, hγ_mass, hγ_bary, hγ_pot⟩

/-! ### Section 3: `integralE` bridge, dyadic approximation, and convex orders -/

private lemma toENNReal_coe_real (r : ℝ) : (r : EReal).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

private lemma integralE_of_nonneg {μ : Measure ℝ} {φ : ℝ → ℝ} (hnn : ∀ x, 0 ≤ φ x) :
    MartOT.Var.integralE μ φ = ((∫⁻ x, ENNReal.ofReal (φ x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have hpos : (fun x => ((φ x : EReal)).toENNReal) = fun x => ENNReal.ofReal (φ x) := by
    ext x; exact toENNReal_coe_real (φ x)
  have hneg : (fun x => (-(φ x : EReal)).toENNReal) = fun _ => 0 := by
    ext x
    rw [← EReal.coe_neg, toENNReal_coe_real, ENNReal.ofReal_eq_zero]
    linarith [hnn x]
  rw [hpos, hneg, lintegral_zero]
  simp

private lemma integralE_of_integrable {μ : Measure ℝ} {φ : ℝ → ℝ} (hφ : Integrable φ μ) :
    MartOT.Var.integralE μ φ = ((∫ x, φ x ∂μ : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have hpos_eq : (fun x => ((φ x : EReal)).toENNReal) = fun x => ENNReal.ofReal (max (φ x) 0) := by
    ext x
    rw [toENNReal_coe_real]
    rcases le_or_gt (φ x) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h.le]
  have hneg_eq : (fun x => (-(φ x : EReal)).toENNReal) = fun x => ENNReal.ofReal (max (-φ x) 0) := by
    ext x
    rw [← EReal.coe_neg, toENNReal_coe_real]
    rcases le_or_gt (-φ x) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h.le]
  have hint_pos : Integrable (fun x => max (φ x) 0) μ := hφ.sup (integrable_zero _ _ _)
  have hint_neg : Integrable (fun x => max (-φ x) 0) μ := hφ.neg.sup (integrable_zero _ _ _)
  rw [hpos_eq, hneg_eq,
    ← ofReal_integral_eq_lintegral_ofReal hint_pos (Eventually.of_forall fun _ => le_max_right _ _),
    ← ofReal_integral_eq_lintegral_ofReal hint_neg (Eventually.of_forall fun _ => le_max_right _ _)]
  have hnn1 : 0 ≤ ∫ x, max (φ x) 0 ∂μ := integral_nonneg fun _ => le_max_right _ _
  have hnn2 : 0 ≤ ∫ x, max (-φ x) 0 ∂μ := integral_nonneg fun _ => le_max_right _ _
  rw [EReal.coe_ennreal_ofReal, max_eq_left hnn1, EReal.coe_ennreal_ofReal, max_eq_left hnn2,
    ← EReal.coe_sub, ← integral_sub hint_pos hint_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rcases le_or_gt 0 (φ x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h.le, max_eq_left (by linarith)]; ring

private lemma integralE_convex_decomp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    let a := rderiv φ 0
    let c := φ 0
    let ψ : ℝ → ℝ := fun y => φ y - (a * y + c)
    MartOT.Var.integralE μ φ =
      ((∫⁻ y, ENNReal.ofReal (ψ y) ∂μ : ENNReal) : EReal) + ((a * bary μ + c * mass μ : ℝ) : EReal) := by
  have : IsFiniteMeasure μ := hμ.1
  intro a c ψ
  have hψ_nn : ∀ y, 0 ≤ ψ y := fun y => by
    have h := rderiv_support_line hφ 0 y
    simp only [sub_zero] at h
    dsimp [ψ, a, c]
    linarith
  have hℓ_int : Integrable (fun y : ℝ => a * y + c) μ :=
    (hμ.2.const_mul a).add (integrable_const c)
  have hℓ_val : ∫ y, (a * y + c) ∂μ = a * bary μ + c * mass μ := by
    rw [integral_add (hμ.2.const_mul a) (integrable_const c), integral_const_mul, integral_const,
      smul_eq_mul, Measure.real_def]
    unfold bary mass
    ring
  have hφ_meas : Measurable φ := (convexOn_continuous hφ).measurable
  have hψ_meas : Measurable ψ := hφ_meas.sub ((measurable_const.mul measurable_id).add measurable_const)
  by_cases hfin : ∫⁻ y, ENNReal.ofReal (ψ y) ∂μ < ⊤
  · have hψ_int : Integrable ψ μ := by
      refine ⟨hψ_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hψ_nn)]
      exact hfin
    have hφ_int : Integrable φ μ := by
      have heq : φ = fun y => ψ y + (a * y + c) := by ext y; dsimp [ψ]; ring
      rw [heq]
      exact hψ_int.add hℓ_int
    rw [integralE_of_integrable hφ_int]
    have hsum : ∫ y, φ y ∂μ = (∫ y, ψ y ∂μ) + (∫ y, (a * y + c) ∂μ) := by
      rw [← integral_add hψ_int hℓ_int]
      congr 1 with y; dsimp [ψ]; ring
    rw [hsum, hℓ_val, EReal.coe_add,
      ← ofReal_integral_eq_lintegral_ofReal hψ_int (Eventually.of_forall hψ_nn),
      EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg hψ_nn)]
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, EReal.coe_ennreal_top, EReal.top_add_coe]
    unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
    have hpos_top : ∫⁻ y, ((φ y : EReal)).toENNReal ∂μ = ⊤ := by
      have hle' : ∀ y, ENNReal.ofReal (ψ y) ≤ ((φ y : EReal)).toENNReal + ENNReal.ofReal |a * y + c| := by
        intro y
        rw [toENNReal_coe_real]
        rcases le_or_gt 0 (φ y) with h | h
        · rw [← ENNReal.ofReal_add h (abs_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          dsimp [ψ]; linarith [neg_le_abs (a * y + c)]
        · rw [ENNReal.ofReal_of_nonpos h.le, zero_add]
          apply ENNReal.ofReal_le_ofReal
          dsimp [ψ]; linarith [neg_le_abs (a * y + c)]
      have hsum_top : ⊤ ≤ (∫⁻ y, ((φ y : EReal)).toENNReal ∂μ) +
          ∫⁻ y, ENNReal.ofReal |a * y + c| ∂μ := by
        rw [← hfin, ← lintegral_add_right _ (by measurability)]
        exact lintegral_mono hle'
      have hℓ_lt : ∫⁻ y, ENNReal.ofReal |a * y + c| ∂μ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hℓ_int.abs (Eventually.of_forall fun _ => abs_nonneg _)]
        exact ENNReal.ofReal_lt_top
      by_contra hne
      have hlt : ∫⁻ y, ((φ y : EReal)).toENNReal ∂μ < ⊤ := lt_top_iff_ne_top.mpr hne
      exact not_lt_of_ge hsum_top (ENNReal.add_lt_top.mpr ⟨hlt, hℓ_lt⟩)
    have hneg_lt : ∫⁻ y, (-(φ y : EReal)).toENNReal ∂μ < ⊤ := by
      have hle : ∀ y, (-(φ y : EReal)).toENNReal ≤ ENNReal.ofReal |a * y + c| := by
        intro y
        rw [← EReal.coe_neg, toENNReal_coe_real]
        apply ENNReal.ofReal_le_ofReal
        have := hψ_nn y
        dsimp [ψ] at this
        linarith [neg_le_abs (a * y + c)]
      have hℓ_lt : ∫⁻ y, ENNReal.ofReal |a * y + c| ∂μ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hℓ_int.abs (Eventually.of_forall fun _ => abs_nonneg _)]
        exact ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt (lintegral_mono hle) hℓ_lt
    rw [hpos_top, EReal.coe_ennreal_top]
    have hne : ((∫⁻ y, (-(φ y : EReal)).toENNReal ∂μ : ENNReal) : EReal) ≠ ⊤ := by
      rw [ne_eq, EReal.coe_ennreal_eq_top_iff]
      exact hneg_lt.ne
    exact EReal.top_sub hne

/-- Dyadic grid point `min (⌊2^n * t⌋₊ / 2^n) n`. -/
private noncomputable def dyadicFloor (n : ℕ) (t : ℝ) : ℝ :=
  min ((Nat.floor ((2 : ℝ) ^ n * t) : ℝ) / (2 : ℝ) ^ n) (n : ℝ)

private lemma dyadicFloor_mono_n (t : ℝ) (ht : 0 ≤ t) : Monotone (fun n => dyadicFloor n t) := by
  refine monotone_nat_of_le_succ fun n => ?_
  unfold dyadicFloor
  refine le_min ?_ ?_
  · refine (min_le_left _ _).trans ?_
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [pow_succ, div_le_div_iff₀ h2 (by positivity)]
    have hfl : 2 * Nat.floor ((2 : ℝ) ^ n * t) ≤ Nat.floor ((2 : ℝ) ^ n * 2 * t) := by
      refine Nat.le_floor ?_
      have hle : (Nat.floor ((2 : ℝ) ^ n * t) : ℝ) ≤ (2 : ℝ) ^ n * t :=
        Nat.floor_le (mul_nonneg h2.le ht)
      push_cast
      linarith
    have hfl_r : (2 : ℝ) * (Nat.floor ((2 : ℝ) ^ n * t) : ℝ) ≤
        (Nat.floor ((2 : ℝ) ^ n * 2 * t) : ℝ) := by exact_mod_cast hfl
    nlinarith
  · refine (min_le_right _ _).trans ?_
    exact_mod_cast Nat.le_succ n

private lemma dyadicFloor_le_self (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : dyadicFloor n t ≤ t := by
  refine (min_le_left _ _).trans ?_
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [div_le_iff₀ h2]
  have := Nat.floor_le (mul_nonneg h2.le ht)
  linarith

private lemma sub_inv_pow_lt_dyadicFloor {n : ℕ} {t : ℝ} (_ht0 : 0 ≤ t) (htn : t ≤ n) :
    t - 1 / (2 : ℝ) ^ n < dyadicFloor n t := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  refine lt_min ?_ ?_
  · rw [lt_div_iff₀ h2]
    have hfl := Nat.lt_floor_add_one ((2 : ℝ) ^ n * t)
    have heq : (t - 1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = (2 : ℝ) ^ n * t - 1 := by
      field_simp [h2.ne']
    linarith
  · have : (0 : ℝ) < 1 / (2 : ℝ) ^ n := by positivity
    linarith

private lemma dyadicFloor_mono_t (n : ℕ) : Monotone (dyadicFloor n) := by
  intro s t hst
  unfold dyadicFloor
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  refine min_le_min_right _ (div_le_div_of_nonneg_right ?_ h2.le)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left hst h2.le)

private lemma integral_indicator_Ici_zero {c y : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) :
    ∫ t in (0 : ℝ)..y, (Ici c).indicator (fun _ => (1 : ℝ)) t = max (y - c) 0 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable ((Ici c).indicator (fun _ => (1 : ℝ))) volume a b := by
    intro a b
    have hm : Monotone ((Ici c).indicator (fun _ => (1 : ℝ))) := by
      intro s t hst
      by_cases hs : c ≤ s
      · simp [Set.indicator_of_mem (show s ∈ Ici c from hs),
          Set.indicator_of_mem (show t ∈ Ici c from hs.trans hst)]
      · simp only [Set.indicator_of_notMem (show s ∉ Ici c from hs)]
        by_cases ht : c ≤ t
        · simp [Set.indicator_of_mem (show t ∈ Ici c from ht)]
        · simp [Set.indicator_of_notMem (show t ∉ Ici c from ht)]
    exact hm.intervalIntegrable
  rcases le_or_gt y c with hle | hlt
  · rw [max_eq_right (sub_nonpos.mpr hle), intervalIntegral.integral_of_le hy]
    have hzero : ∫ t in Ioc 0 y, (Ici c).indicator (fun _ => (1 : ℝ)) t = ∫ _ in Ioc 0 y, (0 : ℝ) := by
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      have hne : ∀ᵐ t ∂volume, t ≠ c := by
        rw [ae_iff]; simp
      filter_upwards [hne] with t htc ht
      have hlt' : t < c := lt_of_le_of_ne (ht.2.trans hle) htc
      exact Set.indicator_of_notMem (not_le.mpr hlt') _
    simp [hzero]
  · rw [max_eq_left (sub_nonneg.mpr hlt.le),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 c) (hint c y)]
    have hleft : ∫ t in (0 : ℝ)..c, (Ici c).indicator (fun _ => (1 : ℝ)) t = 0 := by
      rw [intervalIntegral.integral_of_le hc]
      have hzero : ∫ t in Ioc 0 c, (Ici c).indicator (fun _ => (1 : ℝ)) t = ∫ _ in Ioc 0 c, (0 : ℝ) := by
        refine setIntegral_congr_ae measurableSet_Ioc ?_
        have hne : ∀ᵐ t ∂volume, t ≠ c := by rw [ae_iff]; simp
        filter_upwards [hne] with t htc ht
        exact Set.indicator_of_notMem (not_le.mpr (lt_of_le_of_ne ht.2 htc)) _
      simp [hzero]
    have hright : ∫ t in c..y, (Ici c).indicator (fun _ => (1 : ℝ)) t = y - c := by
      rw [intervalIntegral.integral_of_le hlt.le]
      have hone : ∫ t in Ioc c y, (Ici c).indicator (fun _ => (1 : ℝ)) t = ∫ _ in Ioc c y, (1 : ℝ) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        exact Set.indicator_of_mem (show c ≤ t from ht.1.le) _
      rw [hone, setIntegral_const, smul_eq_mul, mul_one, Measure.real_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hlt.le)]
    rw [hleft, hright, zero_add]

/-- Core step of Prop 4.2(a): if `call α ≤ call β`, then for every convex `ψ ≥ 0` with `ψ 0 = 0`,
`∫⁻ y, ofReal (ψ (max y 0)) ∂α ≤ ∫⁻ y, ofReal (ψ (max y 0)) ∂β`. -/
private lemma lintegral_convex_pos_part_le {α β : Measure ℝ}
    (hα : MartOT.Var.InM α) (hβ : MartOT.Var.InM β)
    (hcall : ∀ x, call α x ≤ call β x)
    {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) (hψ0 : ψ 0 = 0) (hψ_nn : ∀ y, 0 ≤ ψ y) :
    ∫⁻ y, ENNReal.ofReal (ψ (max y 0)) ∂α ≤ ∫⁻ y, ENNReal.ofReal (ψ (max y 0)) ∂β := by
  have hD_mono : Monotone (rderiv ψ) := rderiv_mono hψ
  have hD0_nn : 0 ≤ rderiv ψ 0 := by
    have hslope : Tendsto (fun t => (ψ t - ψ 0) / (t - 0)) (𝓝[>] 0) (𝓝 (rderiv ψ 0)) := by
      have hd := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (rderiv_hasDerivWithinAt hψ 0)
      exact hd.congr fun t => slope_def_field ψ 0 t
    refine ge_of_tendsto hslope ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hψ0, sub_zero, sub_zero]
    exact div_nonneg (hψ_nn t) ht.le
  -- Define explicit piecewise-linear approximations
  let tgrid : ℕ → ℕ → ℝ := fun n k => (k : ℝ) / (2 : ℝ) ^ n
  let N : ℕ → ℕ := fun n => n * 2 ^ n
  let approx : ℕ → ℝ → ℝ := fun n y =>
    rderiv ψ 0 * max y 0 +
      ∑ k ∈ Finset.range (N n),
        (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) * max (y - tgrid n (k + 1)) 0
  -- Identity: approx n y = ∫ t in 0..max y 0, rderiv ψ (dyadicFloor n t)
  have happrox_eq : ∀ n y, approx n y = ∫ t in (0 : ℝ)..max y 0, rderiv ψ (dyadicFloor n t) := by
    intro n y
    have hstep_eq : ∀ t, 0 ≤ t →
        rderiv ψ (dyadicFloor n t) =
          rderiv ψ 0 + ∑ k ∈ Finset.range (N n),
            (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
              (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t := by
      intro t ht
      have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      set j := min (Nat.floor ((2 : ℝ) ^ n * t)) (N n)
      have hj_le : j ≤ N n := min_le_right _ _
      have hdyad : dyadicFloor n t = tgrid n j := by
        unfold dyadicFloor tgrid
        dsimp only [j]
        rcases le_or_gt (Nat.floor ((2 : ℝ) ^ n * t)) (N n) with hle | hlt
        · rw [min_eq_left hle]
          have hle_r : (Nat.floor ((2 : ℝ) ^ n * t) : ℝ) / (2 : ℝ) ^ n ≤ n := by
            rw [div_le_iff₀ h2]
            have : (Nat.floor ((2 : ℝ) ^ n * t) : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hle
            simpa [N, mul_comm] using this
          exact min_eq_left hle_r
        · rw [min_eq_right hlt.le]
          have hgt_r : (n : ℝ) ≤ (Nat.floor ((2 : ℝ) ^ n * t) : ℝ) / (2 : ℝ) ^ n := by
            rw [le_div_iff₀ h2]
            have : (N n : ℝ) ≤ (Nat.floor ((2 : ℝ) ^ n * t) : ℝ) := by exact_mod_cast hlt.le
            simpa [N, mul_comm] using this
          rw [min_eq_right hgt_r]
          simp only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          field_simp [h2.ne']
      have hind_iff : ∀ k ∈ Finset.range (N n),
          (tgrid n (k + 1) ≤ t ↔ k < j) := by
        intro k hk
        have hkN : k < N n := Finset.mem_range.mp hk
        simp only [tgrid, div_le_iff₀ h2]
        constructor
        · intro hle
          have hle' : k + 1 ≤ Nat.floor ((2 : ℝ) ^ n * t) :=
            Nat.le_floor (by push_cast at hle ⊢; linarith)
          exact lt_min (Nat.lt_of_succ_le hle') hkN
        · intro hlt
          have h1 : k + 1 ≤ Nat.floor ((2 : ℝ) ^ n * t) := Nat.succ_le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _))
          have h2' : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n * t :=
            (Nat.cast_le.mpr h1).trans (Nat.floor_le (mul_nonneg h2.le ht))
          push_cast at h2' ⊢
          linarith
      have hsum : ∑ k ∈ Finset.range (N n),
          (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
            (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t =
          ∑ k ∈ Finset.range j, (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) := by
        rw [← Finset.sum_subset (Finset.range_mono hj_le)]
        · refine Finset.sum_congr rfl fun k hk => ?_
          have hkN : k ∈ Finset.range (N n) := Finset.range_mono hj_le hk
          have hmem : t ∈ Ici (tgrid n (k + 1)) := (hind_iff k hkN).mpr (Finset.mem_range.mp hk)
          simp [Set.indicator_of_mem hmem]
        · intro k hkN hkj
          have hnmem : t ∉ Ici (tgrid n (k + 1)) := by
            intro hm
            exact hkj (Finset.mem_range.mpr ((hind_iff k hkN).mp hm))
          simp [Set.indicator_of_notMem hnmem]
      rw [hsum, Finset.sum_range_sub (fun k => rderiv ψ (tgrid n k)) j, hdyad]
      have ht0 : tgrid n 0 = 0 := by simp [tgrid]
      rw [ht0]
      ring
    have hymax : 0 ≤ max y 0 := le_max_right _ _
    have hint_step : ∀ k, IntervalIntegrable (fun t =>
        (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
          (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t) volume 0 (max y 0) := by
      intro k
      have hm : Monotone ((Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ))) := by
        intro s t hst
        by_cases hs : tgrid n (k + 1) ≤ s
        · simp [Set.indicator_of_mem (show s ∈ Ici _ from hs),
            Set.indicator_of_mem (show t ∈ Ici _ from hs.trans hst)]
        · simp only [Set.indicator_of_notMem (show s ∉ Ici _ from hs)]
          by_cases ht : tgrid n (k + 1) ≤ t
          · simp [Set.indicator_of_mem (show t ∈ Ici _ from ht)]
          · simp [Set.indicator_of_notMem (show t ∉ Ici _ from ht)]
      exact hm.intervalIntegrable.const_mul _
    have hcongr : ∫ t in (0 : ℝ)..max y 0, rderiv ψ (dyadicFloor n t) =
        ∫ t in (0 : ℝ)..max y 0, (rderiv ψ 0 + ∑ k ∈ Finset.range (N n),
          (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
            (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hymax] at ht
      exact hstep_eq t ht.1
    have hsum_int : IntervalIntegrable (fun t => ∑ k ∈ Finset.range (N n),
        (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
          (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t) volume 0 (max y 0) := by
      have hfun : (fun t => ∑ k ∈ Finset.range (N n),
          (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
            (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t) =
          ∑ k ∈ Finset.range (N n), fun t =>
            (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
              (Ici (tgrid n (k + 1))).indicator (fun _ => (1 : ℝ)) t := by
        ext t; simp [Finset.sum_apply]
      rw [hfun]
      exact IntervalIntegrable.sum (Finset.range (N n)) fun k _ => hint_step k
    rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const hsum_int,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm (max y 0),
      intervalIntegral.integral_finsetSum (fun k _ => hint_step k)]
    dsimp only [approx]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul,
      integral_indicator_Ici_zero (by unfold tgrid; positivity) hymax]
    congr 1
    rcases le_or_gt y 0 with hy0 | hy0
    · rw [max_eq_right hy0, zero_sub,
        max_eq_right (neg_nonpos.mpr (by unfold tgrid; positivity)),
        max_eq_right (sub_nonpos.mpr (hy0.trans (by unfold tgrid; positivity)))]
    · rw [max_eq_left hy0.le]
  -- Monotonicity in n and pointwise convergence to ψ (max y 0)
  have happrox_mono : ∀ y, Monotone (fun n => ENNReal.ofReal (approx n y)) := by
    intro y i j hij
    apply ENNReal.ofReal_le_ofReal
    rw [happrox_eq i y, happrox_eq j y]
    exact intervalIntegral.integral_mono_on (le_max_right _ _)
      (hD_mono.comp (dyadicFloor_mono_t i)).intervalIntegrable
      (hD_mono.comp (dyadicFloor_mono_t j)).intervalIntegrable
      fun t ht => hD_mono (dyadicFloor_mono_n t ht.1 hij)
  have happrox_sup : ∀ y, (⨆ n, ENNReal.ofReal (approx n y)) = ENNReal.ofReal (ψ (max y 0)) := by
    intro y
    refine tendsto_nhds_unique (tendsto_atTop_iSup (happrox_mono y)) ?_
    refine ENNReal.tendsto_ofReal ?_
    rcases le_or_gt y 0 with hy0 | hy0
    · rw [max_eq_right hy0, hψ0]
      refine tendsto_const_nhds.congr fun n => ?_
      rw [happrox_eq n y, max_eq_right hy0, intervalIntegral.integral_same]
    · rw [max_eq_left hy0.le]
      have hψ_cont : Continuous ψ := convexOn_continuous hψ
      have hlow : Tendsto (fun n : ℕ => ψ (y - 1 / (2 : ℝ) ^ n) - ψ (-(1 / (2 : ℝ) ^ n)))
          atTop (𝓝 (ψ y)) := by
        have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
          simpa [one_div] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 : ℝ) / 2 < 1)
        have h1 : Tendsto (fun n : ℕ => ψ (y - 1 / (2 : ℝ) ^ n)) atTop (𝓝 (ψ y)) := by
          have hc : Tendsto (fun n : ℕ => y - 1 / (2 : ℝ) ^ n) atTop (𝓝 y) := by
            simpa using tendsto_const_nhds.sub hinv
          exact (hψ_cont.continuousAt.tendsto).comp hc
        have h2 : Tendsto (fun n : ℕ => ψ (-(1 / (2 : ℝ) ^ n))) atTop (𝓝 (ψ 0)) := by
          have hc : Tendsto (fun n : ℕ => -(1 / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
            simpa using hinv.neg
          exact (hψ_cont.continuousAt.tendsto).comp hc
        simpa [hψ0] using h1.sub h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · obtain ⟨M, hM⟩ := exists_nat_ge y
        filter_upwards [eventually_ge_atTop M] with n hn
        have hyn : y ≤ n := hM.trans (Nat.cast_le.mpr hn)
        rw [happrox_eq n y, max_eq_left hy0.le]
        have hsub : ψ (y - 1 / (2 : ℝ) ^ n) - ψ (-(1 / (2 : ℝ) ^ n)) =
            ∫ t in (0 : ℝ)..y, rderiv ψ (t - 1 / (2 : ℝ) ^ n) := by
          rw [intervalIntegral.integral_comp_sub_right (rderiv ψ) (1 / (2 : ℝ) ^ n), zero_sub,
            ← sub_eq_integral_rderiv hψ (by linarith)]
        rw [hsub]
        exact intervalIntegral.integral_mono_on hy0.le
          (hD_mono.comp (fun _ _ h => by linarith)).intervalIntegrable
          (hD_mono.comp (dyadicFloor_mono_t n)).intervalIntegrable
          fun t ht => hD_mono (sub_inv_pow_lt_dyadicFloor ht.1 (ht.2.trans hyn)).le
      · refine Eventually.of_forall fun n => ?_
        rw [happrox_eq n y, max_eq_left hy0.le]
        have hψy : ψ y = ∫ t in (0 : ℝ)..y, rderiv ψ t := by
          have := sub_eq_integral_rderiv hψ hy0.le
          linarith [hψ0]
        rw [hψy]
        exact intervalIntegral.integral_mono_on hy0.le
          (hD_mono.comp (dyadicFloor_mono_t n)).intervalIntegrable
          hD_mono.intervalIntegrable
          fun t ht => hD_mono (dyadicFloor_le_self n ht.1)
  -- Compare integrals of approx n for α and β
  have happrox_le : ∀ n,
      ∫⁻ y, ENNReal.ofReal (approx n y) ∂α ≤ ∫⁻ y, ENNReal.ofReal (approx n y) ∂β := by
    intro n
    have hcoeff_nn : ∀ k, 0 ≤ rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k) := fun k => by
      refine sub_nonneg.mpr (hD_mono ?_)
      unfold tgrid
      exact div_le_div_of_nonneg_right (by push_cast; linarith) (by positivity)
    have hsplit : ∀ μ : Measure ℝ, MartOT.Var.InM μ →
        ∫⁻ y, ENNReal.ofReal (approx n y) ∂μ =
          ENNReal.ofReal (rderiv ψ 0) * ENNReal.ofReal (call μ 0) +
            ∑ k ∈ Finset.range (N n),
              ENNReal.ofReal (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
                ENNReal.ofReal (call μ (tgrid n (k + 1))) := by
      intro μ hμ
      have hpt : ∀ y, ENNReal.ofReal (approx n y) =
          ENNReal.ofReal (rderiv ψ 0) * ENNReal.ofReal (max (y - 0) 0) +
            ∑ k ∈ Finset.range (N n),
              ENNReal.ofReal (rderiv ψ (tgrid n (k + 1)) - rderiv ψ (tgrid n k)) *
                ENNReal.ofReal (max (y - tgrid n (k + 1)) 0) := by
        intro y
        dsimp only [approx]
        rw [ENNReal.ofReal_add (mul_nonneg hD0_nn (le_max_right _ _))
            (Finset.sum_nonneg fun k _ => mul_nonneg (hcoeff_nn k) (le_max_right _ _)),
          ENNReal.ofReal_mul hD0_nn, sub_zero,
          ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hcoeff_nn k) (le_max_right _ _))]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ENNReal.ofReal_mul (hcoeff_nn k)
      have hm_c : ∀ c : ℝ, Measurable (fun y : ℝ => ENNReal.ofReal (max (y - c) 0)) :=
        fun c => by fun_prop
      have hm_term : ∀ a c : ℝ, Measurable (fun y : ℝ => ENNReal.ofReal a * ENNReal.ofReal (max (y - c) 0)) :=
        fun a c => measurable_const.mul (hm_c c)
      simp_rw [hpt]
      rw [lintegral_add_left (hm_term _ _),
        lintegral_const_mul _ (hm_c 0),
        lintegral_finsetSum _ fun k _ => hm_term _ _]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_call hμ 0)
        (Eventually.of_forall fun _ => le_max_right _ _)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lintegral_const_mul _ (hm_c _),
        ← ofReal_integral_eq_lintegral_ofReal (integrable_call hμ _)
          (Eventually.of_forall fun _ => le_max_right _ _)]
      rfl
    rw [hsplit α hα, hsplit β hβ]
    refine add_le_add ?_ (Finset.sum_le_sum fun k _ => ?_)
    · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hcall 0))
    · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hcall _))
  -- Apply Monotone Convergence (lintegral_iSup)
  have hmeas_approx : ∀ n, Measurable (fun y => ENNReal.ofReal (approx n y)) := by
    intro n
    dsimp only [approx]
    refine Measurable.ennreal_ofReal ?_
    refine (measurable_const.mul (measurable_id.sup measurable_const)).add ?_
    exact Finset.measurable_sum _ fun k _ =>
      measurable_const.mul ((measurable_id.sub measurable_const).sup measurable_const)
  have hsup_eq : (fun y => ENNReal.ofReal (ψ (max y 0))) = fun y => ⨆ n, ENNReal.ofReal (approx n y) :=
    funext fun y => (happrox_sup y).symm
  rw [hsup_eq, lintegral_iSup hmeas_approx (fun i j hij y => happrox_mono y hij),
    lintegral_iSup hmeas_approx (fun i j hij y => happrox_mono y hij)]
  exact iSup_mono happrox_le

/-- If `call α ≤ call β` and `put α ≤ put β`, then `∫⁻ ofReal (ψ y) ∂α ≤ ∫⁻ ofReal (ψ y) ∂β`
for every nonnegative convex `ψ` with `ψ 0 = 0`. -/
private lemma lintegral_convex_zero_le {α β : Measure ℝ}
    (hα : MartOT.Var.InM α) (hβ : MartOT.Var.InM β)
    (hcall : ∀ x, call α x ≤ call β x) (hput : ∀ x, put α x ≤ put β x)
    {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) (hψ0 : ψ 0 = 0) (hψ_nn : ∀ y, 0 ≤ ψ y) :
    ∫⁻ y, ENNReal.ofReal (ψ y) ∂α ≤ ∫⁻ y, ENNReal.ofReal (ψ y) ∂β := by
  have hsplit : ∀ y, ENNReal.ofReal (ψ y) =
      ENNReal.ofReal (ψ (max y 0)) + ENNReal.ofReal (ψ (-(max (-y) 0))) := by
    intro y
    rw [← ENNReal.ofReal_add (hψ_nn _) (hψ_nn _)]
    congr 1
    rcases le_or_gt 0 y with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -y ≤ 0), neg_zero, hψ0, add_zero]
    · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -y), neg_neg, hψ0, zero_add]
  rw [lintegral_congr hsplit, lintegral_congr hsplit]
  have hm1 : Measurable (fun y => ENNReal.ofReal (ψ (max y 0))) :=
    ((convexOn_continuous hψ).measurable.comp (measurable_id.sup measurable_const)).ennreal_ofReal
  rw [lintegral_add_left hm1, lintegral_add_left hm1]
  refine add_le_add (lintegral_convex_pos_part_le hα hβ hcall hψ hψ0 hψ_nn) ?_
  -- Reduce negative part via reflection y ↦ -y
  let α' := α.map Neg.neg
  let β' := β.map Neg.neg
  have hneg_inM : ∀ μ : Measure ℝ, MartOT.Var.InM μ → MartOT.Var.InM (μ.map Neg.neg) := by
    intro μ hμ
    have : IsFiniteMeasure μ := hμ.1
    refine ⟨Measure.isFiniteMeasure_map μ Neg.neg, ?_⟩
    rw [integrable_map_measure (g := fun x : ℝ => x) (by fun_prop) measurable_neg.aemeasurable]
    exact hμ.2.neg
  have hcall_neg : ∀ μ : Measure ℝ, MartOT.Var.InM μ → ∀ x, call (μ.map Neg.neg) x = put μ (-x) := by
    intro μ _ x
    unfold call put
    rw [integral_map measurable_neg.aemeasurable (f := fun y : ℝ => max (y - x) 0) (by fun_prop)]
    congr 1 with y
    have : -y - x = -x - y := by ring
    rw [this]
  let ψ' : ℝ → ℝ := fun y => ψ (-y)
  have hψ' : ConvexOn ℝ univ ψ' := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hc := hψ.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    dsimp only [ψ']
    have heq : -(a * x + b * y) = a * -x + b * -y := by ring
    rw [heq]
    exact hc
  have hψ'0 : ψ' 0 = 0 := by simp [ψ', hψ0]
  have hψ'_nn : ∀ y, 0 ≤ ψ' y := fun y => hψ_nn (-y)
  have hmap_eq : ∀ μ : Measure ℝ,
      ∫⁻ y, ENNReal.ofReal (ψ (-(max (-y) 0))) ∂μ = ∫⁻ y, ENNReal.ofReal (ψ' (max y 0)) ∂(μ.map Neg.neg) := by
    intro μ
    have hψ'_meas : Measurable (fun y : ℝ => ENNReal.ofReal (ψ' (max y 0))) :=
      ((convexOn_continuous hψ').measurable.comp (by fun_prop)).ennreal_ofReal
    rw [lintegral_map hψ'_meas measurable_neg]
  rw [hmap_eq α, hmap_eq β]
  exact lintegral_convex_pos_part_le (hneg_inM α hα) (hneg_inM β hβ)
    (fun x => by rw [hcall_neg α hα x, hcall_neg β hβ x]; exact hput (-x)) hψ' hψ'0 hψ'_nn

private lemma convexLE_forward {α β : Measure ℝ} (h : MartOT.Var.ConvexLE α β) :
    mass α = mass β ∧ bary α = bary β ∧ ∀ x, MartOT.Var.potential α x ≤ MartOT.Var.potential β x := by
  obtain ⟨hα, hβ, hle⟩ := h
  have : IsFiniteMeasure α := hα.1
  have : IsFiniteMeasure β := hβ.1
  have h1 : mass α ≤ mass β := by
    have := hle (fun _ => (1 : ℝ)) (convexOn_const 1 convex_univ)
    rw [integralE_of_integrable (integrable_const 1), integralE_of_integrable (integrable_const 1)] at this
    simpa [mass, Measure.real_def] using EReal.coe_le_coe_iff.mp this
  have h2 : mass β ≤ mass α := by
    have := hle (fun _ => (-1 : ℝ)) (convexOn_const (-1) convex_univ)
    rw [integralE_of_integrable (integrable_const (-1)), integralE_of_integrable (integrable_const (-1))] at this
    have h' := EReal.coe_le_coe_iff.mp this
    simp only [integral_const, smul_eq_mul, Measure.real_def] at h'
    unfold mass; linarith
  have hm : mass α = mass β := le_antisymm h1 h2
  have hb1 : bary α ≤ bary β := by
    have := hle (fun y => y) (convexOn_id convex_univ)
    rw [integralE_of_integrable hα.2, integralE_of_integrable hβ.2] at this
    exact EReal.coe_le_coe_iff.mp this
  have hb2 : bary β ≤ bary α := by
    have hneg_conv : ConvexOn ℝ univ (fun y : ℝ => -y) := (concaveOn_id convex_univ).neg
    have := hle (fun y => -y) hneg_conv
    have hαn : Integrable (fun y : ℝ => -y) α := hα.2.neg
    have hβn : Integrable (fun y : ℝ => -y) β := hβ.2.neg
    rw [integralE_of_integrable hαn, integralE_of_integrable hβn] at this
    have h' := EReal.coe_le_coe_iff.mp this
    rw [integral_neg (fun y : ℝ => y), integral_neg (fun y : ℝ => y)] at h'
    unfold bary; linarith
  have hb : bary α = bary β := le_antisymm hb1 hb2
  have hp : ∀ x, MartOT.Var.potential α x ≤ MartOT.Var.potential β x := by
    intro x
    have hconv : ConvexOn ℝ univ (fun y : ℝ => |y - x|) := by
      refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
      simp only [smul_eq_mul]
      have heq : a * y + b * z - x = a * (y - x) + b * (z - x) := by
        calc a * y + b * z - x = a * y + b * z - (a + b) * x := by rw [hab, one_mul]
          _ = a * (y - x) + b * (z - x) := by ring
      rw [heq]
      calc |a * (y - x) + b * (z - x)| ≤ |a * (y - x)| + |b * (z - x)| := abs_add_le _ _
        _ = a * |y - x| + b * |z - x| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have := hle (fun y => |y - x|) hconv
    rw [integralE_of_integrable (integrable_abs_sub hα x),
      integralE_of_integrable (integrable_abs_sub hβ x)] at this
    exact EReal.coe_le_coe_iff.mp this
  exact ⟨hm, hb, hp⟩

/-- **Proposition 4.2(a) (backward direction)**: equal mass and `u_α ≤ u_β` implies `α ⪯C β`. -/
private lemma convexLE_of_potential_le {α β : Measure ℝ}
    (hα : MartOT.Var.InM α) (hβ : MartOT.Var.InM β)
    (hm : mass α = mass β) (hp : ∀ x, MartOT.Var.potential α x ≤ MartOT.Var.potential β x) :
    MartOT.Var.ConvexLE α β := by
  -- Equal mass + u_α ≤ u_β forces equal barycenter from asymptotics!
  have hb : bary α = bary β := by
    have htop := (potential_tendsto_right_asymp hβ).sub (potential_tendsto_right_asymp hα)
    have hbot := (potential_tendsto_left_asymp hβ).sub (potential_tendsto_left_asymp hα)
    have h1 : bary β ≤ bary α := by
      have hlim : Tendsto (fun x => MartOT.Var.potential β x - MartOT.Var.potential α x)
          atTop (𝓝 (bary α - bary β)) := by
        have := htop.add_const (bary α - bary β)
        rw [sub_self, zero_add] at this
        refine this.congr fun x => ?_
        rw [hm]; ring
      have hnn := ge_of_tendsto hlim (Eventually.of_forall fun x => sub_nonneg.mpr (hp x))
      linarith
    have h2 : bary α ≤ bary β := by
      have hlim : Tendsto (fun x => MartOT.Var.potential β x - MartOT.Var.potential α x)
          atBot (𝓝 (bary β - bary α)) := by
        have := hbot.add_const (bary β - bary α)
        rw [sub_self, zero_add] at this
        refine this.congr fun x => ?_
        rw [hm]; ring
      have hnn := ge_of_tendsto hlim (Eventually.of_forall fun x => sub_nonneg.mpr (hp x))
      linarith
    exact le_antisymm h2 h1
  have hcall : ∀ x, call α x ≤ call β x := fun x => by
    have h1 := potential_sub_right_asymp hα x
    have h2 := potential_sub_right_asymp hβ x
    rw [hm, hb] at h1
    linarith [hp x]
  have hput : ∀ x, put α x ≤ put β x := fun x => by
    have h1 := potential_sub_left_asymp hα x
    have h2 := potential_sub_left_asymp hβ x
    rw [hm, hb] at h1
    linarith [hp x]
  refine ⟨hα, hβ, fun φ hφ => ?_⟩
  rw [integralE_convex_decomp hα hφ, integralE_convex_decomp hβ hφ, hm, hb]
  refine add_le_add ?_ le_rfl
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  let ψ : ℝ → ℝ := fun y => φ y - (rderiv φ 0 * y + φ 0)
  have hψ : ConvexOn ℝ univ ψ := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, ψ]
    have h1 := hφ.2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h1
    have h2 : rderiv φ 0 * (a * x + b * y) + φ 0 =
        a * (rderiv φ 0 * x + φ 0) + b * (rderiv φ 0 * y + φ 0) := by
      calc rderiv φ 0 * (a * x + b * y) + φ 0 = rderiv φ 0 * (a * x + b * y) + (a + b) * φ 0 := by
            rw [hab, one_mul]
        _ = a * (rderiv φ 0 * x + φ 0) + b * (rderiv φ 0 * y + φ 0) := by ring
    linarith
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψ_nn : ∀ y, 0 ≤ ψ y := fun y => by
    have := rderiv_support_line hφ 0 y
    simp only [sub_zero] at this
    dsimp [ψ]; linarith
  exact lintegral_convex_zero_le hα hβ hcall hput hψ hψ0 hψ_nn

private lemma extConvexLE_forward {μ ν : Measure ℝ} (h : MartOT.Var.ExtConvexLE μ ν) :
    mass μ ≤ mass ν ∧ (∀ x, call μ x ≤ call ν x) ∧ (∀ x, put μ x ≤ put ν x) := by
  obtain ⟨hμ, hν, hle⟩ := h
  have : IsFiniteMeasure μ := hμ.1
  have : IsFiniteMeasure ν := hν.1
  have hm : mass μ ≤ mass ν := by
    have := hle (fun _ => (1 : ℝ)) (convexOn_const 1 convex_univ) (fun _ => zero_le_one)
    simp only [ENNReal.ofReal_one, lintegral_const, one_mul] at this
    exact ENNReal.toReal_mono (measure_ne_top ν univ) this
  have hcall : ∀ x, call μ x ≤ call ν x := by
    intro x
    have hlin : ConvexOn ℝ univ (fun y : ℝ => y - x) :=
      (convexOn_id convex_univ).sub (concaveOn_const x convex_univ)
    have hconv : ConvexOn ℝ univ (fun y : ℝ => max (y - x) 0) :=
      hlin.sup (convexOn_const 0 convex_univ)
    have h1 := hle (fun y => max (y - x) 0) hconv (fun _ => le_max_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_call hμ x) (Eventually.of_forall fun _ => le_max_right _ _),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_call hν x) (Eventually.of_forall fun _ => le_max_right _ _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)).mp h1
  have hput : ∀ x, put μ x ≤ put ν x := by
    intro x
    have hlin : ConvexOn ℝ univ (fun y : ℝ => x - y) :=
      (convexOn_const x convex_univ).sub (concaveOn_id convex_univ)
    have hconv : ConvexOn ℝ univ (fun y : ℝ => max (x - y) 0) :=
      hlin.sup (convexOn_const 0 convex_univ)
    have h1 := hle (fun y => max (x - y) 0) hconv (fun _ => le_max_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_put hμ x) (Eventually.of_forall fun _ => le_max_right _ _),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_put hν x) (Eventually.of_forall fun _ => le_max_right _ _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)).mp h1
  exact ⟨hm, hcall, hput⟩

private lemma extConvexLE_of_convexLE_of_le {α θ β : Measure ℝ}
    (hαθ : MartOT.Var.ConvexLE α θ) (hθβ : θ ≤ β) (hβ : MartOT.Var.InM β) :
    MartOT.Var.ExtConvexLE α β := by
  refine ⟨hαθ.1, hβ, fun φ hφ hnn => ?_⟩
  have h1 := hαθ.2.2 φ hφ
  rw [integralE_of_nonneg hnn, integralE_of_nonneg hnn, EReal.coe_ennreal_le_coe_ennreal_iff] at h1
  exact h1.trans (lintegral_mono' hθβ le_rfl)

/-! ### Section 4: Convex envelope `convEnv` and convexity of `u_ν - convEnv (u_ν - u_μ)` -/

private noncomputable def convEnv (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ ψ : ℝ → ℝ, ConvexOn ℝ univ ψ ∧ (∀ y, ψ y ≤ g y) ∧ ψ x = v}

private lemma le_convEnv {g ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) (hle : ∀ y, ψ y ≤ g y) (x : ℝ) :
    ψ x ≤ convEnv g x := by
  refine le_csSup ?_ ⟨ψ, hψ, hle, rfl⟩
  exact ⟨g x, by rintro _ ⟨φ, _, hφg, rfl⟩; exact hφg x⟩

private lemma convEnv_le {g ψ₀ : ℝ → ℝ} (hψ₀ : ConvexOn ℝ univ ψ₀) (hle : ∀ y, ψ₀ y ≤ g y) (x : ℝ) :
    convEnv g x ≤ g x := by
  refine csSup_le ⟨ψ₀ x, ψ₀, hψ₀, hle, rfl⟩ ?_
  rintro _ ⟨φ, _, hφg, rfl⟩
  exact hφg x

private lemma convEnv_convexOn {g ψ₀ : ℝ → ℝ} (hψ₀ : ConvexOn ℝ univ ψ₀) (hle : ∀ y, ψ₀ y ≤ g y) :
    ConvexOn ℝ univ (convEnv g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine csSup_le ⟨ψ₀ (a * x + b * y), ψ₀, hψ₀, hle, rfl⟩ ?_
  rintro _ ⟨φ, hφ, hφg, rfl⟩
  have h1 := hφ.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h1
  exact h1.trans (add_le_add (mul_le_mul_of_nonneg_left (le_convEnv hφ hφg x) ha)
    (mul_le_mul_of_nonneg_left (le_convEnv hφ hφg y) hb))

/-- On `{x | convEnv g x < g x}`, `convEnv g` is locally affine (has locally constant `rderiv`). -/
private lemma convEnv_locally_affine {g ψ₀ : ℝ → ℝ}
    (hg : Continuous g) (hψ₀ : ConvexOn ℝ univ ψ₀) (hle : ∀ y, ψ₀ y ≤ g y)
    {x₀ : ℝ} (hlt : convEnv g x₀ < g x₀) :
    ∃ x₁ x₂ : ℝ, x₁ < x₀ ∧ x₀ < x₂ ∧
      ∀ y ∈ Icc x₁ x₂, convEnv g y =
        convEnv g x₁ + (convEnv g x₂ - convEnv g x₁) / (x₂ - x₁) * (y - x₁) := by
  set h := convEnv g
  have hh_conv : ConvexOn ℝ univ h := convEnv_convexOn hψ₀ hle
  have hh_cont : Continuous h := convexOn_continuous hh_conv
  set δ := (g x₀ - h x₀) / 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hnhds_g : ∀ᶠ y in 𝓝 x₀, g x₀ - δ < g y :=
    hg.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  have hnhds_h : ∀ᶠ y in 𝓝 x₀, h y < h x₀ + δ :=
    hh_cont.continuousAt.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hnhds_g.and hnhds_h)
  set η := ε / 2
  have hη : 0 < η := by positivity
  set x₁ := x₀ - η
  set x₂ := x₀ + η
  have hx₁₂ : x₁ < x₂ := by dsimp only [x₁, x₂]; linarith
  have hsub_pos : 0 < x₂ - x₁ := sub_pos.mpr hx₁₂
  set s := (h x₂ - h x₁) / (x₂ - x₁)
  let ℓ : ℝ → ℝ := fun y => h x₁ + s * (y - x₁)
  have hℓ_conv : ConvexOn ℝ univ ℓ := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, ℓ]
    have : a * (h x₁ + s * (u - x₁)) + b * (h x₁ + s * (v - x₁)) =
        (a + b) * h x₁ + s * (a * u + b * v - (a + b) * x₁) := by ring
    rw [this, hab, one_mul, one_mul]
  let htilde : ℝ → ℝ := fun y => max (h y) (ℓ y)
  have htilde_conv : ConvexOn ℝ univ htilde := hh_conv.sup hℓ_conv
  have htilde_le_g : ∀ y, htilde y ≤ g y := by
    intro y
    refine max_le (convEnv_le hψ₀ hle y) ?_
    by_cases hy : y ∈ Icc x₁ x₂
    · have hdist : dist y x₀ < ε := by
        rw [Real.dist_eq, abs_lt]
        have hy1 : x₀ - η ≤ y := hy.1
        have hy2 : y ≤ x₀ + η := hy.2
        dsimp only [η] at hy1 hy2
        constructor <;> linarith
      have hdist1 : dist x₁ x₀ < ε := by
        rw [Real.dist_eq, show x₁ - x₀ = -η by ring, abs_neg, abs_of_pos hη]
        dsimp only [η]; linarith
      have hdist2 : dist x₂ x₀ < ε := by
        rw [Real.dist_eq, show x₂ - x₀ = η by ring, abs_of_pos hη]
        dsimp only [η]; linarith
      have hgy := (hball hdist).1
      have hh1 := (hball hdist1).2
      have hh2 := (hball hdist2).2
      have hgap : h x₀ + δ < g x₀ - δ := by dsimp only [δ]; linarith
      set t := (y - x₁) / (x₂ - x₁)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hy.1) hsub_pos.le
      have ht1 : t ≤ 1 := (div_le_one hsub_pos).mpr (sub_le_sub_right hy.2 x₁)
      have hℓ_eq : ℓ y = (1 - t) * h x₁ + t * h x₂ := by
        dsimp only [ℓ, s, t]
        field_simp [hsub_pos.ne']
        ring
      rw [hℓ_eq]
      nlinarith
    · -- Outside [x₁, x₂], convexity of h gives ℓ y ≤ h y ≤ g y!
      have hℓ_le_h : ℓ y ≤ h y := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hy
        rcases hy with hlt1 | hgt2
        · have hsec := hh_conv.slope_mono_adjacent (mem_univ y) (mem_univ x₂) hlt1 hx₁₂
          -- hsec : (h x₁ - h y) / (x₁ - y) ≤ (h x₂ - h x₁) / (x₂ - x₁) = s
          have h1 : h x₁ - h y ≤ s * (x₁ - y) := (div_le_iff₀ (sub_pos.mpr hlt1)).mp hsec
          dsimp only [ℓ]; linarith
        · have hsec := hh_conv.slope_mono_adjacent (mem_univ x₁) (mem_univ y) hx₁₂ hgt2
          -- hsec : s = (h x₂ - h x₁) / (x₂ - x₁) ≤ (h y - h x₂) / (y - x₂)
          have h1 : s * (y - x₂) ≤ h y - h x₂ := (le_div_iff₀ (sub_pos.mpr hgt2)).mp hsec
          have h2 : h x₂ = h x₁ + s * (x₂ - x₁) := by
            dsimp only [s]; field_simp [hsub_pos.ne']; ring
          dsimp only [ℓ]; linarith
      exact hℓ_le_h.trans (convEnv_le hψ₀ hle y)
  have htilde_le_h : ∀ y, htilde y ≤ h y := fun y => le_convEnv htilde_conv htilde_le_g y
  refine ⟨x₁, x₂, by linarith, by linarith, fun y hy => ?_⟩
  have hge : ℓ y ≤ h y := (le_max_right (h y) (ℓ y)).trans (htilde_le_h y)
  have hle' : h y ≤ ℓ y := by
    set t := (y - x₁) / (x₂ - x₁)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hy.1) hsub_pos.le
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ((div_le_one hsub_pos).mpr (sub_le_sub_right hy.2 x₁))
    have hy_eq : (1 - t) * x₁ + t * x₂ = y := by
      dsimp only [t]; field_simp [hsub_pos.ne']; ring
    have hℓ_eq : (1 - t) * h x₁ + t * h x₂ = ℓ y := by
      dsimp only [ℓ, s, t]; field_simp [hsub_pos.ne']; ring
    have hc := hh_conv.2 (mem_univ x₁) (mem_univ x₂) ht1 ht0 (by ring)
    simp only [smul_eq_mul, hy_eq, hℓ_eq] at hc
    exact hc
  exact le_antisymm hle' hge

/-- If `convEnv g < g` on `(u, v)`, then `convEnv g` is affine on `[u, v]`. -/
private lemma convEnv_affine_on_Icc {g ψ₀ : ℝ → ℝ}
    (hg : Continuous g) (hψ₀ : ConvexOn ℝ univ ψ₀) (hle : ∀ y, ψ₀ y ≤ g y)
    {u v : ℝ} (huv : u < v) (hlt : ∀ y ∈ Ioo u v, convEnv g y < g y) :
    ∀ y ∈ Icc u v, convEnv g y =
      convEnv g u + (convEnv g v - convEnv g u) / (v - u) * (y - u) := by
  set h := convEnv g
  have hh_conv : ConvexOn ℝ univ h := convEnv_convexOn hψ₀ hle
  have hh_cont : Continuous h := convexOn_continuous hh_conv
  have hD_mono : Monotone (rderiv h) := rderiv_mono hh_conv
  -- Locally constant rderiv on (u, v)
  have hD_loc : ∀ z ∈ Ioo u v, ∃ z₁ z₂, z₁ < z ∧ z < z₂ ∧
      ∀ w ∈ Ioo z₁ z₂, rderiv h w = rderiv h z := by
    intro z hz
    obtain ⟨z₁, z₂, h1, h2, haff⟩ := convEnv_locally_affine hg hψ₀ hle (hlt z hz)
    refine ⟨z₁, z₂, h1, h2, fun w hw => ?_⟩
    set s := (h z₂ - h z₁) / (z₂ - z₁)
    have hD_eq : ∀ p ∈ Ioo z₁ z₂, rderiv h p = s := by
      intro p hp
      have hderiv : HasDerivWithinAt h s (Ioi p) p := by
        have hlin : HasDerivWithinAt (fun y => h z₁ + s * (y - z₁)) s (Ioi p) p := by
          have := ((hasDerivAt_id p).sub_const z₁).const_mul s |>.const_add (h z₁)
          simpa using this.hasDerivWithinAt
        refine hlin.congr_of_eventuallyEq ?_ (haff p ⟨hp.1.le, hp.2.le⟩)
        filter_upwards [Ioo_mem_nhdsGT hp.2] with y hy
        exact haff y ⟨(hp.1.trans hy.1).le, hy.2.le⟩
      exact hderiv.derivWithin (uniqueDiffWithinAt_Ioi p)
    rw [hD_eq w hw, hD_eq z ⟨h1, h2⟩]
  -- Connectedness of (u, v): rderiv h is constant on (u, v)
  have hD_const : ∀ x ∈ Ioo u v, ∀ y ∈ Ioo u v, rderiv h x = rderiv h y := by
    suffices ∀ x ∈ Ioo u v, ∀ y ∈ Ioo u v, x < y → rderiv h x = rderiv h y by
      intro x hx y hy
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · exact this x hx y hy hxy
      · rfl
      · exact (this y hy x hx hyx).symm
    intro x hx y hy hxy
    by_contra hne
    have hltD : rderiv h x < rderiv h y := lt_of_le_of_ne (hD_mono hxy.le) hne
    set S := {w ∈ Icc x y | rderiv h x < rderiv h w}
    have hSne : S.Nonempty := ⟨y, ⟨hxy.le, le_rfl⟩, hltD⟩
    have hSbdd : BddBelow S := ⟨x, fun _ hw => hw.1.1⟩
    set z := sInf S
    have hzx : x ≤ z := le_csInf hSne fun _ hw => hw.1.1
    have hzy : z ≤ y := csInf_le hSbdd ⟨⟨hxy.le, le_rfl⟩, hltD⟩
    have hz_in : z ∈ Ioo u v := ⟨lt_of_lt_of_le hx.1 hzx, lt_of_le_of_lt hzy hy.2⟩
    obtain ⟨z₁, z₂, hz₁, hz₂, hconst⟩ := hD_loc z hz_in
    -- There exists w ∈ S with w < z₂
    obtain ⟨w, hwS, hwz₂⟩ := exists_lt_of_csInf_lt hSne hz₂
    have hzw : z ≤ w := csInf_le hSbdd hwS
    have hw_in : w ∈ Ioo z₁ z₂ := ⟨lt_of_lt_of_le hz₁ hzw, hwz₂⟩
    have hDz_gt : rderiv h x < rderiv h z := by
      rw [← hconst w hw_in]; exact hwS.2
    have hzx_lt : x < z := lt_of_le_of_ne hzx (fun heq => by rw [heq] at hDz_gt; exact lt_irrefl _ hDz_gt)
    -- Pick p ∈ (max x z₁, z)
    obtain ⟨p, hp1, hp2⟩ := exists_between (max_lt hzx_lt hz₁)
    have hp_in : p ∈ Ioo z₁ z₂ := ⟨lt_of_le_of_lt (le_max_right _ _) hp1, hp2.trans hz₂⟩
    have hp_S : p ∈ S := by
      refine ⟨⟨(le_max_left _ _).trans hp1.le, hp2.le.trans hzy⟩, ?_⟩
      rw [hconst p hp_in]; exact hDz_gt
    exact not_lt_of_ge (csInf_le hSbdd hp_S) hp2
  -- Now integrate rderiv h on (u, v) and pass to endpoints by continuity
  obtain ⟨m₀, hm₀⟩ := exists_between huv
  set s := rderiv h m₀
  have hD_eq_s : ∀ t ∈ Ioo u v, rderiv h t = s := fun t ht => hD_const t ht m₀ hm₀
  have haff_Ioo : ∀ p q, u < p → p ≤ q → q < v → h q - h p = s * (q - p) := by
    intro p q hup hpq hqv
    rw [sub_eq_integral_rderiv hh_conv hpq]
    have hcongr : ∫ t in p..q, rderiv h t = ∫ _ in p..q, s := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hpq] at ht
      exact hD_eq_s t ⟨lt_of_lt_of_le hup ht.1, lt_of_le_of_lt ht.2 hqv⟩
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have haff_Icc : ∀ y ∈ Icc u v, h y = h u + s * (y - u) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with rfl | huy
    · simp
    rcases eq_or_lt_of_le hy.2 with hy_eq | hyv
    · -- y = v: approximate u from above and v from below
      have hseq_u : Tendsto (fun n : ℕ => u + (v - u) / (3 * ((n : ℝ) + 1))) atTop (𝓝 u) := by
        have h0 : Tendsto (fun n : ℕ => (v - u) / (3 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
          have : Tendsto (fun n : ℕ => 3 * ((n : ℝ) + 1)) atTop atTop :=
            Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          exact tendsto_const_nhds.div_atTop this
        simpa using tendsto_const_nhds.add h0
      have hseq_v : Tendsto (fun n : ℕ => v - (v - u) / (3 * ((n : ℝ) + 1))) atTop (𝓝 v) := by
        have h0 : Tendsto (fun n : ℕ => (v - u) / (3 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
          have : Tendsto (fun n : ℕ => 3 * ((n : ℝ) + 1)) atTop atTop :=
            Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          exact tendsto_const_nhds.div_atTop this
        simpa using tendsto_const_nhds.sub h0
      have hL := (hh_cont.continuousAt.tendsto.comp hseq_v).sub (hh_cont.continuousAt.tendsto.comp hseq_u)
      have hR := (hseq_v.sub hseq_u).const_mul s
      have heq_n : ∀ n : ℕ,
          h (v - (v - u) / (3 * ((n : ℝ) + 1))) - h (u + (v - u) / (3 * ((n : ℝ) + 1))) =
            s * ((v - (v - u) / (3 * ((n : ℝ) + 1))) - (u + (v - u) / (3 * ((n : ℝ) + 1)))) := by
        intro n
        have hstep_pos : 0 < (v - u) / (3 * ((n : ℝ) + 1)) := by
          have : 0 < v - u := sub_pos.mpr huv
          positivity
        have hstep_lt : (v - u) / (3 * ((n : ℝ) + 1)) < (v - u) / 2 := by
          have hvu : 0 < v - u := sub_pos.mpr huv
          exact div_lt_div_of_pos_left hvu (by norm_num) (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
        exact haff_Ioo _ _ (by linarith) (by linarith) (by linarith)
      have hv_eq := tendsto_nhds_unique (hL.congr heq_n) hR
      rw [hy_eq]; linarith
    · -- y ∈ (u, v): approximate u from above
      have hseq_u : Tendsto (fun n : ℕ => u + (y - u) / (2 * ((n : ℝ) + 1))) atTop (𝓝 u) := by
        have h0 : Tendsto (fun n : ℕ => (y - u) / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
          have : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
            Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          exact tendsto_const_nhds.div_atTop this
        simpa using tendsto_const_nhds.add h0
      have hL : Tendsto (fun n : ℕ => h y - h (u + (y - u) / (2 * ((n : ℝ) + 1)))) atTop (𝓝 (h y - h u)) :=
        tendsto_const_nhds.sub (hh_cont.continuousAt.tendsto.comp hseq_u)
      have hR : Tendsto (fun n : ℕ => s * (y - (u + (y - u) / (2 * ((n : ℝ) + 1))))) atTop (𝓝 (s * (y - u))) :=
        (tendsto_const_nhds.sub hseq_u).const_mul s
      have heq_n : ∀ n : ℕ,
          h y - h (u + (y - u) / (2 * ((n : ℝ) + 1))) =
            s * (y - (u + (y - u) / (2 * ((n : ℝ) + 1)))) := by
        intro n
        have hstep_pos : 0 < (y - u) / (2 * ((n : ℝ) + 1)) := by
          have : 0 < y - u := sub_pos.mpr huy
          positivity
        have hstep_le : (y - u) / (2 * ((n : ℝ) + 1)) ≤ y - u := by
          have hyu : 0 < y - u := sub_pos.mpr huy
          exact div_le_self hyu.le (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
        exact haff_Ioo _ y (by linarith) (by linarith) hyv
      have hy_eq := tendsto_nhds_unique (hL.congr heq_n) hR
      linarith
  have hs : s = (h v - h u) / (v - u) := by
    have hv := haff_Icc v ⟨huv.le, le_rfl⟩
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    field_simp [hvu]
    linarith
  intro y hy
  rw [← hs]
  exact haff_Icc y hy

/-- **Key convexity theorem**: for convex `u₁, u₂ : ℝ → ℝ` such that `g = u₂ - u₁` has a convex
minorant `ψ₀`, the function `f = u₂ - convEnv g` is convex! -/
private lemma convexOn_sub_convEnv {u₁ u₂ ψ₀ : ℝ → ℝ}
    (hu₁ : ConvexOn ℝ univ u₁) (hu₂ : ConvexOn ℝ univ u₂)
    (hψ₀ : ConvexOn ℝ univ ψ₀) (hle : ∀ y, ψ₀ y ≤ u₂ y - u₁ y) :
    ConvexOn ℝ univ (fun x => u₂ x - convEnv (fun y => u₂ y - u₁ y) x) := by
  let g : ℝ → ℝ := fun y => u₂ y - u₁ y
  let h : ℝ → ℝ := convEnv g
  let f : ℝ → ℝ := fun y => u₂ y - h y
  have hg_cont : Continuous g := (convexOn_continuous hu₂).sub (convexOn_continuous hu₁)
  have hh_conv : ConvexOn ℝ univ h := convEnv_convexOn hψ₀ hle
  have hh_cont : Continuous h := convexOn_continuous hh_conv
  have hf_ge : ∀ y, u₁ y ≤ f y := fun y => by
    have := convEnv_le hψ₀ hle y
    dsimp only [f, h, g] at *
    linarith
  refine ⟨convex_univ, fun a _ b _ t₁ t₂ ht₁ ht₂ hsum => ?_⟩
  simp only [smul_eq_mul]
  -- WLOG a < b, 0 < t₁, 0 < t₂
  rcases eq_or_lt_of_le ht₁ with rfl | ht₁_pos
  · simp [show t₂ = 1 by linarith]
  rcases eq_or_lt_of_le ht₂ with rfl | ht₂_pos
  · simp [show t₁ = 1 by linarith]
  -- Handle a = b, a < b, b < a symmetrically
  suffices hmain : ∀ a' b' t₁' t₂' : ℝ, a' < b' → 0 < t₁' → 0 < t₂' → t₁' + t₂' = 1 →
      f (t₁' * a' + t₂' * b') ≤ t₁' * f a' + t₂' * f b' by
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact hmain a b t₁ t₂ hab ht₁_pos ht₂_pos hsum
    · have : t₁ * a + t₂ * a = a := by linarith [show (t₁ + t₂) * a = a by rw [hsum, one_mul]]
      rw [this]
      linarith [show (t₁ + t₂) * f a = f a by rw [hsum, one_mul]]
    · have h' := hmain b a t₂ t₁ hba ht₂_pos ht₁_pos (by linarith)
      dsimp only [f, h, g] at h'
      rw [add_comm (t₂ * b) (t₁ * a)] at h'
      linarith
  intro a' b' t₁' t₂' hab ht₁' ht₂' hsum'
  set x := t₁' * a' + t₂' * b'
  have hax : a' < x := by
    dsimp only [x]
    have : a' = (t₁' + t₂') * a' := by rw [hsum', one_mul]
    nlinarith
  have hxb : x < b' := by
    dsimp only [x]
    have : b' = (t₁' + t₂') * b' := by rw [hsum', one_mul]
    nlinarith
  let chord : ℝ → ℝ := fun y => f a' + (f b' - f a') / (b' - a') * (y - a')
  have hchord_x : chord x = t₁' * f a' + t₂' * f b' := by
    dsimp only [chord, x]
    have hne : b' - a' ≠ 0 := sub_ne_zero.mpr hab.ne'
    have ht1 : t₁' = 1 - t₂' := by linarith
    rw [ht1]
    field_simp [hne]
    ring
  rw [← hchord_x]
  -- On the contact set C = {y | h y = g y}, f y ≤ chord y for all y ∈ [a', b']
  have hcontact_le : ∀ y ∈ Icc a' b', h y = g y → f y ≤ chord y := by
    intro y hy heq
    have hfy : f y = u₁ y := by dsimp only [f, g] at *; linarith
    set s := (y - a') / (b' - a')
    have hba : 0 < b' - a' := sub_pos.mpr hab
    have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hy.1) hba.le
    have hs1 : 0 ≤ 1 - s := sub_nonneg.mpr ((div_le_one hba).mpr (sub_le_sub_right hy.2 a'))
    have hy_comb : (1 - s) * a' + s * b' = y := by dsimp only [s]; field_simp [hba.ne']; ring
    have hch_y : chord y = (1 - s) * f a' + s * f b' := by dsimp only [chord, s]; field_simp [hba.ne']; ring
    have hc := hu₁.2 (mem_univ a') (mem_univ b') hs1 hs0 (by ring)
    simp only [smul_eq_mul, hy_comb] at hc
    rw [hfy, hch_y]
    exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left (hf_ge a') hs1)
      (mul_le_mul_of_nonneg_left (hf_ge b') hs0))
  by_cases hxC : h x = g x
  · exact hcontact_le x ⟨hax.le, hxb.le⟩ hxC
  have hlt_x : h x < g x := lt_of_le_of_ne (convEnv_le hψ₀ hle x) hxC
  let C : Set ℝ := {y | h y = g y}
  have hC_closed : IsClosed C := isClosed_eq hh_cont hg_cont
  let CL : Set ℝ := C ∩ Icc a' x
  let CR : Set ℝ := C ∩ Icc x b'
  classical
  set u : ℝ := if CL.Nonempty then sSup CL else a'
  set v : ℝ := if CR.Nonempty then sInf CR else b'
  have hu_ge : a' ≤ u := by
    by_cases hne : CL.Nonempty
    · simp only [u, if_pos hne]
      obtain ⟨y, hy⟩ := hne
      exact hy.2.1.trans (le_csSup ⟨x, fun _ hw => hw.2.2⟩ hy)
    · simp [u, if_neg hne]
  have hu_lt : u < x := by
    by_cases hne : CL.Nonempty
    · simp only [u, if_pos hne]
      have hle_x : sSup CL ≤ x := csSup_le hne fun _ hw => hw.2.2
      have hmem : sSup CL ∈ CL := (hC_closed.inter isClosed_Icc).csSup_mem hne ⟨x, fun _ hw => hw.2.2⟩
      exact lt_of_le_of_ne hle_x (fun heq => hxC (heq ▸ hmem.1))
    · simp [u, if_neg hne, hax]
  have hv_le : v ≤ b' := by
    by_cases hne : CR.Nonempty
    · simp only [v, if_pos hne]
      obtain ⟨y, hy⟩ := hne
      exact (csInf_le ⟨x, fun _ hw => hw.2.1⟩ hy).trans hy.2.2
    · simp [v, if_neg hne]
  have hv_gt : x < v := by
    by_cases hne : CR.Nonempty
    · simp only [v, if_pos hne]
      have hge_x : x ≤ sInf CR := le_csInf hne fun _ hw => hw.2.1
      have hmem : sInf CR ∈ CR := (hC_closed.inter isClosed_Icc).csInf_mem hne ⟨x, fun _ hw => hw.2.1⟩
      exact lt_of_le_of_ne hge_x (fun heq => hxC (heq.symm ▸ hmem.1))
    · simp [v, if_neg hne, hxb]
  have hu_chord : f u ≤ chord u := by
    by_cases hne : CL.Nonempty
    · simp only [u, if_pos hne]
      have hmem : sSup CL ∈ CL := (hC_closed.inter isClosed_Icc).csSup_mem hne ⟨x, fun _ hw => hw.2.2⟩
      exact hcontact_le _ ⟨hmem.2.1, hmem.2.2.trans hxb.le⟩ hmem.1
    · simp [u, if_neg hne, chord]
  have hv_chord : f v ≤ chord v := by
    by_cases hne : CR.Nonempty
    · simp only [v, if_pos hne]
      have hmem : sInf CR ∈ CR := (hC_closed.inter isClosed_Icc).csInf_mem hne ⟨x, fun _ hw => hw.2.1⟩
      exact hcontact_le _ ⟨hax.le.trans hmem.2.1, hmem.2.2⟩ hmem.1
    · simp only [v, if_neg hne, chord]
      have hne' : b' - a' ≠ 0 := sub_ne_zero.mpr hab.ne'
      have heq : f a' + (f b' - f a') / (b' - a') * (b' - a') = f b' := by
        field_simp [hne']; ring
      linarith
  -- On (u, v), h < g
  have hlt_Ioo : ∀ y ∈ Ioo u v, h y < g y := by
    intro y hy
    refine lt_of_le_of_ne (convEnv_le hψ₀ hle y) ?_
    intro heq
    rcases le_or_gt y x with hyx | hxy
    · have hyCL : y ∈ CL := ⟨heq, hu_ge.trans hy.1.le, hyx⟩
      have hne : CL.Nonempty := ⟨y, hyCL⟩
      have hle_u : y ≤ u := by
        simp only [u, if_pos hne]
        exact le_csSup ⟨x, fun _ hw => hw.2.2⟩ hyCL
      linarith [hy.1]
    · have hyCR : y ∈ CR := ⟨heq, hxy.le, hy.2.le.trans hv_le⟩
      have hne : CR.Nonempty := ⟨y, hyCR⟩
      have hge_v : v ≤ y := by
        simp only [v, if_pos hne]
        exact csInf_le ⟨x, fun _ hw => hw.2.1⟩ hyCR
      linarith [hy.2]
  -- Hence h is affine on [u, v]
  have haff := convEnv_affine_on_Icc hg_cont hψ₀ hle (hu_lt.trans hv_gt) hlt_Ioo
  set θ := (x - u) / (v - u)
  have hvu : 0 < v - u := sub_pos.mpr (hu_lt.trans hv_gt)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hu_lt.le) hvu.le
  have hθ1 : 0 ≤ 1 - θ := sub_nonneg.mpr ((div_le_one hvu).mpr (sub_le_sub_right hv_gt.le u))
  have hx_comb : (1 - θ) * u + θ * v = x := by dsimp only [θ]; field_simp [hvu.ne']; ring
  have hh_x : h x = (1 - θ) * h u + θ * h v := by
    have := haff x ⟨hu_lt.le, hv_gt.le⟩
    dsimp only [h, g, θ] at this ⊢
    field_simp [hvu.ne'] at this ⊢
    linarith
  have hu₂_x : u₂ x ≤ (1 - θ) * u₂ u + θ * u₂ v := by
    have hc := hu₂.2 (mem_univ u) (mem_univ v) hθ1 hθ0 (by ring)
    simpa [smul_eq_mul, hx_comb] using hc
  have hf_x : f x ≤ (1 - θ) * f u + θ * f v := by
    dsimp only [f]
    linarith
  have hchord_comb : (1 - θ) * chord u + θ * chord v = chord x := by
    dsimp only [chord]
    have hlin : (1 - θ) * (u - a') + θ * (v - a') = x - a' := by linarith [hx_comb]
    calc (1 - θ) * (f a' + (f b' - f a') / (b' - a') * (u - a')) +
          θ * (f a' + (f b' - f a') / (b' - a') * (v - a'))
        = f a' + (f b' - f a') / (b' - a') * ((1 - θ) * (u - a') + θ * (v - a')) := by ring
      _ = f a' + (f b' - f a') / (b' - a') * (x - a') := by rw [hlin]
  rw [← hchord_comb]
  exact hf_x.trans (add_le_add (mul_le_mul_of_nonneg_left hu_chord hθ1)
    (mul_le_mul_of_nonneg_left hv_chord hθ0))

/-! ### Section 5: Existence, uniqueness, and property (iii′) of the shadow -/

private lemma shadow_exists {μ ν : Measure ℝ}
    (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (hE : MartOT.Var.ExtConvexLE μ ν) :
    ∃ η : Measure ℝ, MartOT.Var.IsShadow ν μ η := by
  obtain ⟨hm_le, hcall_le, hput_le⟩ := extConvexLE_forward hE
  set M := mass ν - mass μ
  set B := bary ν - bary μ
  have hM : 0 ≤ M := sub_nonneg.mpr hm_le
  let g : ℝ → ℝ := fun x => MartOT.Var.potential ν x - MartOT.Var.potential μ x
  let ψ₀ : ℝ → ℝ := fun x => |M * x - B|
  have hψ₀_conv : ConvexOn ℝ univ ψ₀ := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, ψ₀]
    have heq : M * (a * x + b * y) - B = a * (M * x - B) + b * (M * y - B) := by
      calc M * (a * x + b * y) - B = M * (a * x + b * y) - (a + b) * B := by rw [hab, one_mul]
        _ = a * (M * x - B) + b * (M * y - B) := by ring
    rw [heq]
    calc |a * (M * x - B) + b * (M * y - B)| ≤ |a * (M * x - B)| + |b * (M * y - B)| := abs_add_le _ _
      _ = a * |M * x - B| + b * |M * y - B| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hψ₀_le : ∀ x, ψ₀ x ≤ g x := by
    intro x
    have h1 : g x - (M * x - B) = 2 * (call ν x - call μ x) := by
      dsimp only [g, M, B]
      linarith [potential_sub_right_asymp hν x, potential_sub_right_asymp hμ x]
    have h2 : g x - (B - M * x) = 2 * (put ν x - put μ x) := by
      dsimp only [g, M, B]
      linarith [potential_sub_left_asymp hν x, potential_sub_left_asymp hμ x]
    have hr : M * x - B ≤ g x := by linarith [hcall_le x]
    have hl : B - M * x ≤ g x := by linarith [hput_le x]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let h : ℝ → ℝ := convEnv g
  let f : ℝ → ℝ := fun x => MartOT.Var.potential ν x - h x
  have hh_conv : ConvexOn ℝ univ h := convEnv_convexOn hψ₀_conv hψ₀_le
  have hf_conv : ConvexOn ℝ univ f :=
    convexOn_sub_convEnv (potential_convexOn hμ) (potential_convexOn hν) hψ₀_conv hψ₀_le
  -- Asymptotics of h
  have hh_top : Tendsto (fun x => h x - (M * x - B)) atTop (𝓝 0) := by
    have hg_top : Tendsto (fun x => g x - (M * x - B)) atTop (𝓝 0) := by
      have h1 := (potential_tendsto_right_asymp hν).sub (potential_tendsto_right_asymp hμ)
      rw [sub_self] at h1
      exact h1.congr fun x => by dsimp only [g, M, B]; ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg_top ?_ ?_
    · intro x
      have := le_convEnv hψ₀_conv hψ₀_le x
      dsimp only [h, ψ₀] at this ⊢
      linarith [le_abs_self (M * x - B)]
    · intro x
      exact sub_le_sub_right (convEnv_le hψ₀_conv hψ₀_le x) _
  have hh_bot : Tendsto (fun x => h x - (B - M * x)) atBot (𝓝 0) := by
    have hg_bot : Tendsto (fun x => g x - (B - M * x)) atBot (𝓝 0) := by
      have h1 := (potential_tendsto_left_asymp hν).sub (potential_tendsto_left_asymp hμ)
      rw [sub_self] at h1
      exact h1.congr fun x => by dsimp only [g, M, B]; ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg_bot ?_ ?_
    · intro x
      have := le_convEnv hψ₀_conv hψ₀_le x
      dsimp only [h, ψ₀] at this ⊢
      linarith [neg_le_abs (M * x - B)]
    · intro x
      exact sub_le_sub_right (convEnv_le hψ₀_conv hψ₀_le x) _
  -- Asymptotics of f = u_ν - h
  have hf_top : Tendsto (fun x => f x - (mass μ * x - bary μ)) atTop (𝓝 0) := by
    have h1 := (potential_tendsto_right_asymp hν).sub hh_top
    rw [sub_self] at h1
    exact h1.congr fun x => by dsimp only [f, M, B]; ring
  have hf_bot : Tendsto (fun x => f x - (bary μ - mass μ * x)) atBot (𝓝 0) := by
    have h1 := (potential_tendsto_left_asymp hν).sub hh_bot
    rw [sub_self] at h1
    exact h1.congr fun x => by dsimp only [f, M, B]; ring
  -- Reconstruct measures λ (potential h) and η (potential f)
  obtain ⟨lam, hlam_inM, _, _, hlam_pot⟩ := exists_measure_of_potential hh_conv hM hh_top hh_bot
  obtain ⟨η, hη_inM, hη_mass, _, hη_pot⟩ :=
    exists_measure_of_potential hf_conv ENNReal.toReal_nonneg hf_top hf_bot
  -- η + lam = ν, hence η ≤ ν
  have hadd_eq : η + lam = ν := by
    refine eq_of_potential_eq (inM_add hη_inM hlam_inM) hν fun x => ?_
    rw [potential_add hη_inM hlam_inM x, hη_pot x, hlam_pot x]
    dsimp only [f]; ring
  have hη_le_ν : η ≤ ν := by
    rw [← hadd_eq]
    exact Measure.le_add_right le_rfl
  -- μ ⪯C η
  have hμη : MartOT.Var.ConvexLE μ η := by
    refine convexLE_of_potential_le hμ hη_inM hη_mass.symm fun x => ?_
    rw [hη_pot x]
    have := convEnv_le hψ₀_conv hψ₀_le x
    dsimp only [f, h, g] at this ⊢
    linarith
  -- Property (iii): for any η' ≤ ν with μ ⪯C η', η ⪯C η'
  refine ⟨η, hη_le_ν, hμη, fun η' hη'_le hμη' => ?_⟩
  have hη'_inM : MartOT.Var.InM η' := hμη'.2.1
  have : IsFiniteMeasure η' := hη'_inM.1
  let lam' := ν - η'
  have hadd' : lam' + η' = ν := Measure.sub_add_cancel_of_le hη'_le
  have hlam'_le : lam' ≤ ν := by
    rw [← hadd']; exact Measure.le_add_right le_rfl
  have hlam'_inM : MartOT.Var.InM lam' := inM_of_le hν hlam'_le
  have hlam'_pot : ∀ x, MartOT.Var.potential lam' x = MartOT.Var.potential ν x - MartOT.Var.potential η' x := by
    intro x
    have := potential_add hlam'_inM hη'_inM x
    rw [hadd'] at this
    linarith
  obtain ⟨hm', _, hp'⟩ := convexLE_forward hμη'
  have hlam'_le_g : ∀ x, MartOT.Var.potential lam' x ≤ g x := fun x => by
    rw [hlam'_pot x]
    dsimp only [g]
    linarith [hp' x]
  have hlam'_le_h : ∀ x, MartOT.Var.potential lam' x ≤ h x := fun x =>
    le_convEnv (potential_convexOn hlam'_inM) hlam'_le_g x
  refine convexLE_of_potential_le hη_inM hη'_inM (hη_mass.trans hm') fun x => ?_
  rw [hη_pot x]
  have := hlam'_le_h x
  rw [hlam'_pot x] at this
  dsimp only [f]
  linarith

private lemma shadow_unique {μ ν η₁ η₂ : Measure ℝ}
    (h₁ : MartOT.Var.IsShadow ν μ η₁) (h₂ : MartOT.Var.IsShadow ν μ η₂) :
    η₁ = η₂ := by
  have h12 : MartOT.Var.ConvexLE η₁ η₂ := h₁.2.2 η₂ h₂.1 h₂.2.1
  have h21 : MartOT.Var.ConvexLE η₂ η₁ := h₂.2.2 η₁ h₁.1 h₁.2.1
  have hp12 := (convexLE_forward h12).2.2
  have hp21 := (convexLE_forward h21).2.2
  exact eq_of_potential_eq h12.1 h12.2.1 fun x => le_antisymm (hp12 x) (hp21 x)

end MartOTShadowHelpers

theorem solution (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (h : MartOT.Var.ExtConvexLE μ ν) :
    (∃! η : Measure ℝ, MartOT.Var.IsShadow ν μ η) ∧
    ∀ η : Measure ℝ, MartOT.Var.IsShadow ν μ η →
      ∀ η' : Measure ℝ, η' ≤ ν → MartOT.Var.ExtConvexLE μ η' → MartOT.Var.ExtConvexLE η η' := by
  constructor
  · obtain ⟨η, hη⟩ := shadow_exists hμ hν h
    exact ⟨η, hη, fun η' hη' => shadow_unique hη' hη⟩
  · intro η hη η' hη'_le hμη'
    obtain ⟨θ, hθ⟩ := shadow_exists hμη'.1 hμη'.2.1 hμη'
    have hηθ : MartOT.Var.ConvexLE η θ := hη.2.2 θ (hθ.1.trans hη'_le) hθ.2.1
    exact extConvexLE_of_convexLE_of_le hηθ hθ.1 hμη'.2.1
