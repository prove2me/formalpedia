-- Prove2me | solution 1 for LiqProvision.Oligopoly.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:46:27.28859+00:00
-- url     : https://prove2.me/submissions/e558f738-acf1-44b5-a350-e65b716ea825

import Mathlib

open Set MeasureTheory Filter Topology

namespace LiqC2Aux

theorem identity (f g : ℝ → ℝ) (hfint : IntegrableOn f (Ioi 0))
    (hgloc : ∀ y, 0 ≤ y → IntegrableOn g (Icc 0 y)) (y : ℝ) (hy : 0 < y) :
    ∫ x in (0:ℝ)..y, g x * ∫ t in Ioi x, f t =
      (∫ x in (0:ℝ)..y, (∫ t in (0:ℝ)..x, g t) * f x) +
        (∫ t in (0:ℝ)..y, g t) * ∫ t in Ioi y, f t := by
  set μ := (volume : Measure ℝ).restrict (Ioc 0 y) with hμ
  have hgI : Integrable g μ := (hgloc y hy.le).mono_set Ioc_subset_Icc_self
  have hfI : Integrable f μ := hfint.mono_set Ioc_subset_Ioi_self
  set k : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => g p.1 * f p.2) with hk
  have hkI : Integrable k (μ.prod μ) :=
    (hgI.mul_prod hfI).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hswap := integral_integral_swap (f := fun x t => k (x, t)) hkI
  have hin1 : ∀ x ∈ Ioc 0 y, ∫ t, k (x, t) ∂μ = g x * ∫ t in Ioc x y, f t := by
    intro x hx
    have : (fun t => k (x, t)) = fun t => g x * (Ioi x).indicator f t := by
      funext t; by_cases h : x < t <;> simp [hk, h]
    have hs : Ioi x ∩ Ioc 0 y = Ioc x y := by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hx.1.trans h1, h3⟩
    rw [this, integral_const_mul, integral_indicator measurableSet_Ioi, hμ,
      Measure.restrict_restrict measurableSet_Ioi, hs]
  have hin2 : ∀ t ∈ Ioc 0 y, ∫ x, k (x, t) ∂μ = (∫ s in (0:ℝ)..t, g s) * f t := by
    intro t ht
    have : (fun x => k (x, t)) = fun x => (Iio t).indicator g x * f t := by
      funext x; by_cases h : x < t <;> simp [hk, h]
    have hs : Iio t ∩ Ioc 0 y = Ioo 0 t := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.le.trans ht.2⟩
    rw [this, integral_mul_const, integral_indicator measurableSet_Iio, hμ,
      Measure.restrict_restrict measurableSet_Iio, intervalIntegral.integral_of_le ht.1.le,
      integral_Ioc_eq_integral_Ioo, hs]
  have hsplit : ∀ x ∈ Ioc 0 y, ∫ t in Ioi x, f t = (∫ t in Ioc x y, f t) + ∫ t in Ioi y, f t := by
    intro x hx
    rw [← Ioc_union_Ioi_eq_Ioi hx.2, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hfint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hx.1.le)))
      (hfint.mono_set (Ioi_subset_Ioi hy.le))]
  rw [intervalIntegral.integral_of_le hy.le, intervalIntegral.integral_of_le hy.le,
    intervalIntegral.integral_of_le hy.le]
  have hA : Integrable (fun x => ∫ t, k (x, t) ∂μ) μ := hkI.integral_prod_left
  calc ∫ x in Ioc 0 y, g x * ∫ t in Ioi x, f t
      = ∫ x in Ioc 0 y, ((∫ t, k (x, t) ∂μ) + g x * ∫ t in Ioi y, f t) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx; simp only; rw [hin1 x hx, hsplit x hx]; ring
    _ = (∫ x, ∫ t, k (x, t) ∂μ ∂μ) + (∫ x in Ioc 0 y, g x) * ∫ t in Ioi y, f t := by
        rw [integral_add hA (hgI.mul_const _), integral_mul_const]
    _ = _ := by
        rw [hswap]
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht; exact hin2 t ht

end LiqC2Aux

open LiqC2Aux in
theorem solution (f g H : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hfint : MeasureTheory.IntegrableOn f (Set.Ioi 0))
    (hgloc : ∀ y, 0 ≤ y → MeasureTheory.IntegrableOn g (Set.Icc 0 y))
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hHmono : MonotoneOn H (Set.Ici 0))
    (hGH : ∀ x, 0 ≤ x → |∫ t in (0 : ℝ)..x, g t| ≤ H x)
    (hHf : MeasureTheory.IntegrableOn (fun x => H x * f x) (Set.Ici 0)) :
    Tendsto (fun y => ∫ x in (0 : ℝ)..y, g x * ∫ t in Set.Ioi x, f t) atTop
      (𝓝 (∫ x in Set.Ioi 0, (∫ t in (0 : ℝ)..x, g t) * f x)) := by
  set G : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, g t with hG
  have hGc : ContinuousOn G (Ici 0) := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx
    have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := x + 1)
      (μ := volume) (f := g)
      (by rw [uIcc_of_le (by linarith)]; exact hgloc _ (by linarith))
    rw [uIcc_of_le (by linarith)] at h
    have hxm : x ∈ Icc 0 (x + 1) := ⟨hx0, by linarith⟩
    refine (h x hxm).mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin (Ici 0) (Iic_mem_nhds (by linarith))
  have hGfI : IntegrableOn (fun x => G x * f x) (Ioi 0) := by
    refine Integrable.mono' (hHf.mono_set Ioi_subset_Ici_self) ?_ ?_
    · exact ((hGc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi).mul
        hfint.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : (0:ℝ) ≤ x := le_of_lt hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 x hx0)]
      exact mul_le_mul_of_nonneg_right (hGH x hx0) (hf0 x hx0)
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hGfI tendsto_id
  have htail : Tendsto (fun y => ∫ x in Ioi y, H x * f x) atTop (𝓝 0) := by
    have h2 := intervalIntegral_tendsto_integral_Ioi 0 (hHf.mono_set Ioi_subset_Ici_self)
      tendsto_id
    have hev : ∀ᶠ y in atTop, (∫ x in Ioi (0:ℝ), H x * f x) - ∫ x in (0:ℝ)..id y, H x * f x =
        ∫ x in Ioi y, H x * f x := by
      filter_upwards [eventually_gt_atTop 0] with y hy
      rw [id, intervalIntegral.integral_of_le hy.le, ← Ioc_union_Ioi_eq_Ioi hy.le,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hHf.mono_set (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self))
          (hHf.mono_set ((Ioi_subset_Ioi hy.le).trans Ioi_subset_Ici_self))]
      ring
    have h3 := (tendsto_const_nhds (x := ∫ x in Ioi (0:ℝ), H x * f x)).sub h2
    rw [sub_self] at h3
    exact h3.congr' hev
  have hbd : Tendsto (fun y => G y * ∫ t in Ioi y, f t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ htail
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hF0 : 0 ≤ ∫ t in Ioi y, f t :=
      setIntegral_nonneg measurableSet_Ioi (fun t ht => hf0 t (hy.le.trans (le_of_lt ht)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hF0]
    calc |G y| * ∫ t in Ioi y, f t ≤ H y * ∫ t in Ioi y, f t :=
          mul_le_mul_of_nonneg_right (hGH y hy.le) hF0
      _ = ∫ t in Ioi y, H y * f t := (integral_const_mul _ _).symm
      _ ≤ ∫ t in Ioi y, H t * f t := by
        apply setIntegral_mono_on ((hfint.mono_set (Ioi_subset_Ioi hy.le)).const_mul _)
          (hHf.mono_set ((Ioi_subset_Ioi hy.le).trans Ioi_subset_Ici_self)) measurableSet_Ioi
        intro t ht
        exact mul_le_mul_of_nonneg_right
          (hHmono (mem_Ici.2 hy.le) (mem_Ici.2 (hy.le.trans (le_of_lt ht))) (le_of_lt ht))
          (hf0 t (hy.le.trans (le_of_lt ht)))
  have h4 := h1.add hbd
  rw [add_zero] at h4
  apply h4.congr'
  filter_upwards [eventually_gt_atTop 0] with y hy
  exact (identity f g hfint hgloc y hy).symm
