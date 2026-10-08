-- Prove2me | solution 1 for NestedSeatAlloc.ProbCond.eq27_er1_one_sided_derivs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:20:07.82998+00:00
-- url     : https://prove2.me/submissions/18796707-d2a2-41af-863b-40775278116c

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology in
theorem f090e2d2_rev1 (f p : ℕ → ℝ) (x : ℕ → ℝ) (s : ℝ) :
    NestedSeatAlloc.ProbCond.revenue f p x 1 s = f 1 * min s (x 1) := by
  simp only [NestedSeatAlloc.ProbCond.revenue]
  split_ifs with h
  · rw [min_eq_left h.le]
  · rw [min_eq_right (not_lt.mp h)]

theorem f090e2d2_absmin (t x : ℝ) (hx : 0 ≤ x) : |min t x| ≤ |t| := by
  rcases le_total t x with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hx]
    have : 0 ≤ t := hx.trans h
    rw [abs_of_nonneg this]; exact h

open MeasureTheory Filter in
theorem f090e2d2_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (t : ℝ) :
    Integrable (fun ω => min t (Y ω)) P := by
  refine Integrable.of_bound (C := |t|) ?_ ?_
  · exact (measurable_const.min hY).aestronglyMeasurable
  · exact Eventually.of_forall (fun ω => by
      simpa [Real.norm_eq_abs] using f090e2d2_absmin t (Y ω) (hY0 ω))

theorem f090e2d2_slope_bound (t s x : ℝ) : |(t - s)⁻¹ * (min t x - min s x)| ≤ 1 := by
  rcases eq_or_ne t s with h | h
  · subst h; simp
  · rw [abs_mul, abs_inv]
    have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr h)
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact abs_min_sub_min_le_max t x s x |>.trans (by simp)

open Filter Topology in
theorem f090e2d2_lim_right (s x : ℝ) :
    Tendsto (fun t => (t - s)⁻¹ * (min t x - min s x)) (𝓝[>] s)
      (𝓝 (Set.indicator {y : ℝ | s < y} (fun _ => (1:ℝ)) x)) := by
  by_cases hx : s < x
  · rw [Set.indicator_of_mem (by exact hx)]
    apply tendsto_const_nhds.congr'
    have : Set.Ioo s x ∈ 𝓝[>] s := Ioo_mem_nhdsGT hx
    filter_upwards [this] with t ht
    rw [min_eq_left ht.2.le, min_eq_left hx.le, inv_mul_cancel₀ (sub_ne_zero.mpr ht.1.ne')]
  · rw [Set.indicator_of_notMem (by exact hx)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hxs : x ≤ s := not_lt.mp hx
    have ht' : s < t := ht
    rw [min_eq_right (hxs.trans ht'.le), min_eq_right hxs]; simp

open Filter Topology in
theorem f090e2d2_lim_left (s x : ℝ) :
    Tendsto (fun t => (t - s)⁻¹ * (min t x - min s x)) (𝓝[<] s)
      (𝓝 (Set.indicator {y : ℝ | s ≤ y} (fun _ => (1:ℝ)) x)) := by
  by_cases hx : s ≤ x
  · rw [Set.indicator_of_mem (by exact hx)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t < s := ht
    rw [min_eq_left (ht'.le.trans hx), min_eq_left hx, inv_mul_cancel₀ (sub_ne_zero.mpr ht'.ne)]
  · rw [Set.indicator_of_notMem (by exact hx)]
    have hxs : x < s := not_le.mp hx
    apply tendsto_const_nhds.congr'
    have : Set.Ioo x s ∈ 𝓝[<] s := Ioo_mem_nhdsLT hxs
    filter_upwards [this] with t ht
    rw [min_eq_right ht.1.le, min_eq_right hxs.le]; simp

open MeasureTheory Filter Topology in
theorem f090e2d2_slope_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (s t : ℝ) :
    slope (fun u => ∫ ω, min u (Y ω) ∂P) s t
      = ∫ ω, (t - s)⁻¹ * (min t (Y ω) - min s (Y ω)) ∂P := by
  rw [slope_def_field, integral_const_mul, integral_sub (f090e2d2_integrable P Y hY hY0 t)
    (f090e2d2_integrable P Y hY hY0 s)]
  ring

open MeasureTheory Filter Topology in
theorem f090e2d2_dct {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (s : ℝ)
    (l : Filter ℝ) [l.IsCountablyGenerated] (A : Set ℝ) (hA : MeasurableSet A)
    (hlim : ∀ x, Tendsto (fun t => (t - s)⁻¹ * (min t x - min s x)) l
      (𝓝 (Set.indicator A (fun _ => (1:ℝ)) x))) :
    Tendsto (slope (fun u => ∫ ω, min u (Y ω) ∂P) s) l (𝓝 (P.real (Y ⁻¹' A))) := by
  have hint : ∫ ω, Set.indicator A (fun _ => (1:ℝ)) (Y ω) ∂P = P.real (Y ⁻¹' A) := by
    have : (fun ω => Set.indicator A (fun _ => (1:ℝ)) (Y ω))
        = Set.indicator (Y ⁻¹' A) (fun _ => (1:ℝ)) := by
      funext ω; rfl
    rw [this, integral_indicator_const _ (hY hA)]
    simp
  rw [← hint]
  have hslope : slope (fun u => ∫ ω, min u (Y ω) ∂P) s
      = fun t => ∫ ω, (t - s)⁻¹ * (min t (Y ω) - min s (Y ω)) ∂P := by
    funext t; exact f090e2d2_slope_eq P Y hY hY0 s t
  rw [hslope]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun t =>
      (measurable_const.mul ((measurable_const.min hY).sub (measurable_const.min hY))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun t => Eventually.of_forall (fun ω => by
      simpa [Real.norm_eq_abs] using f090e2d2_slope_bound t s (Y ω)))
  · exact integrable_const _
  · exact Eventually.of_forall (fun ω => hlim (Y ω))

open MeasureTheory in
theorem f090e2d2_concave {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) :
    ConcaveOn ℝ (Set.Ici 0) (fun u => ∫ ω, min u (Y ω) ∂P) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((f090e2d2_integrable P Y hY hY0 x).const_mul a)
      ((f090e2d2_integrable P Y hY hY0 y).const_mul b)]
  refine integral_mono ?_ (f090e2d2_integrable P Y hY hY0 _) ?_
  · exact ((f090e2d2_integrable P Y hY hY0 x).const_mul a).add
      ((f090e2d2_integrable P Y hY hY0 y).const_mul b)
  · intro ω
    simp only
    apply le_min
    · have h1 := mul_le_mul_of_nonneg_left (min_le_left x (Y ω)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_left y (Y ω)) hb
      linarith
    · have h1 := mul_le_mul_of_nonneg_left (min_le_right x (Y ω)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right y (Y ω)) hb
      have : a * Y ω + b * Y ω = Y ω := by rw [← add_mul, hab, one_mul]
      linarith

open MeasureTheory ProbabilityTheory Filter Topology in
theorem f090e2d2_expRev {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) :
    NestedSeatAlloc.ProbCond.expRevenue P X f p 1 = fun s => f 1 * ∫ ω, min s (X 1 ω) ∂P := by
  funext s
  simp only [NestedSeatAlloc.ProbCond.expRevenue, f090e2d2_rev1]
  rw [integral_const_mul]

open NestedSeatAlloc.ProbCond MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hX : Measurable (X 1))
    (hX0 : ∀ ω, 0 ≤ X 1 ω) (hf1 : 0 ≤ f 1) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1) ∧
      (∀ s, 0 ≤ s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s < X 1 ω}) (Set.Ici s) s) ∧
      (∀ s, 0 < s →
        HasDerivWithinAt (expRevenue P X f p 1) (f 1 * P.real {ω | s ≤ X 1 ω}) (Set.Iic s) s) := by
  rw [f090e2d2_expRev]
  refine ⟨?_, ?_, ?_⟩
  · have := (f090e2d2_concave P (X 1) hX hX0).smul hf1
    simpa [Pi.smul_def, smul_eq_mul] using this
  · intro s _
    apply HasDerivWithinAt.const_mul
    rw [hasDerivWithinAt_iff_tendsto_slope,
      show Set.Ici s \ {s} = Set.Ioi s from by ext y; simp [lt_iff_le_and_ne]]
    exact f090e2d2_dct P (X 1) hX hX0 s _ {y | s < y} measurableSet_Ioi
      (f090e2d2_lim_right s)
  · intro s _
    apply HasDerivWithinAt.const_mul
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_sdiff_right]
    exact f090e2d2_dct P (X 1) hX hX0 s _ {y | s ≤ y} measurableSet_Ici
      (f090e2d2_lim_left s)
