-- Prove2me | solution 1 for Grothendieck.integrable_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:47:24.066188+00:00
-- url     : https://prove2.me/submissions/02960fc2-b24f-4b4f-9fca-07eefe916bed

import Mathlib
import Definitions.Def_Grothendieck_Fubini

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

namespace Grothendieck

noncomputable section

/-- The one-dimensional majorant `s ↦ s^{-1/2} (1+2s)^{-(r+2)/2}` is integrable on `(0,∞)` when
`r ≥ 2`. -/
theorem integrableOn_one_dim (r : ℕ) (hr : 2 ≤ r) :
    IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ) * (1 + 2 * s) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      (Set.Ioi (0:ℝ)) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  set c : ℝ := ((r : ℝ) + 2) / 2 with hc_def
  have hc1 : 1 < c := by rw [hc_def]; linarith
  have hc0 : 0 < c := lt_trans one_pos hc1
  -- on `(0,1]` the factor `(1+2s)^{-c}` is at most `1`
  have h1 : IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ) * (1 + 2 * s) ^ (-c))
      (Set.Ioc 0 1) := by
    have hbase : IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ)) (Set.Ioc 0 1) := by
      have hIoo : IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ)) (Set.Ioo 0 1) := by
        rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
        norm_num
      exact hIoo.congr_set_ae Ioo_ae_eq_Ioc.symm
    refine Integrable.mono_nonneg hbase ?_ ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      intro x hx
      have hx0 : (0:ℝ) < x := hx.1
      have hlin : ContinuousAt (fun s : ℝ => 1 + 2 * s) x := by fun_prop
      have hrp : ContinuousAt (fun y : ℝ => y ^ (-c)) (1 + 2 * x) :=
        Real.continuousAt_rpow_const (1 + 2 * x) (-c) (Or.inl (by positivity))
      have h2 : ContinuousAt (fun s : ℝ => (1 + 2 * s) ^ (-c)) x :=
        hrp.comp (f := fun s : ℝ => 1 + 2 * s) hlin
      exact ((Real.continuousAt_rpow_const x (-(1/2)) (Or.inl hx0.ne')).mul h2).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _)
        (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ 1 + 2 * x) _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : (0:ℝ) < x := hx.1
      have hone : (1:ℝ) ≤ 1 + 2 * x := by linarith
      have hle : (1 + 2 * x) ^ (-c) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hone (neg_nonpos.mpr hc0.le)
      calc x ^ (-(1/2) : ℝ) * (1 + 2 * x) ^ (-c) ≤ x ^ (-(1/2) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (le_of_lt hx0) _)
        _ = x ^ (-(1/2) : ℝ) := mul_one _
  -- on `(1,∞)` we may replace `1+2s` by `s`
  have h2 : IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ) * (1 + 2 * s) ^ (-c))
      (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun s : ℝ => s ^ (-(c + 1/2) : ℝ)) (Set.Ioi 1) := by
      refine integrableOn_Ioi_rpow_of_lt ?_ zero_lt_one
      linarith
    refine Integrable.mono_nonneg hbase ?_ ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro x hx
      have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
      have hlin : ContinuousAt (fun s : ℝ => 1 + 2 * s) x := by fun_prop
      have hrp : ContinuousAt (fun y : ℝ => y ^ (-c)) (1 + 2 * x) :=
        Real.continuousAt_rpow_const (1 + 2 * x) (-c) (Or.inl (by positivity))
      have h2 : ContinuousAt (fun s : ℝ => (1 + 2 * s) ^ (-c)) x :=
        hrp.comp (f := fun s : ℝ => 1 + 2 * s) hlin
      exact ((Real.continuousAt_rpow_const x (-(1/2)) (Or.inl hx0.ne')).mul h2).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx1)) _)
        (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + 2 * x) _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx1
      have hle : x ≤ 1 + 2 * x := by linarith
      have hstep : (1 + 2 * x) ^ (-c) ≤ x ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hx0 hle (neg_nonpos.mpr hc0.le)
      have hxhalf : (0:ℝ) ≤ x ^ (-(1/2) : ℝ) := Real.rpow_nonneg (le_of_lt hx0) _
      calc x ^ (-(1/2) : ℝ) * (1 + 2 * x) ^ (-c) ≤ x ^ (-(1/2) : ℝ) * x ^ (-c) :=
            mul_le_mul_of_nonneg_left hstep hxhalf
        _ = x ^ (-(c + 1/2) : ℝ) := by
            rw [← Real.rpow_add hx0]
            congr 1
            ring
  have hunion : IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ) * (1 + 2 * s) ^ (-c))
      (Set.Ioc 0 1 ∪ Set.Ioi 1) := h1.union h2
  have hset : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext x
    constructor
    · rintro (⟨h0, _⟩ | h1)
      · exact h0
      · exact lt_trans (zero_lt_one : (0:ℝ) < 1) (show (1:ℝ) < x from h1)
    · intro hx
      rcases le_or_gt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  rwa [hset] at hunion

/-- **Target A.** For `r ≥ 2` and `τ² < 1` the Laplace kernel of Lemma 2.1 is integrable for the
product of the Lebesgue measure restricted to the positive half-line with itself. -/
theorem integrable_kernel_proof (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      planeMeasure := by
  set c : ℝ := ((r : ℝ) + 2) / 2 with hc_def
  have hc0 : 0 < c := by rw [hc_def]; positivity
  have ht2 : 0 < 1 - τ ^ 2 := by linarith
  -- the one-dimensional majorant is integrable
  have hg : Integrable (fun s : ℝ => s ^ (-(1/2) : ℝ) * (1 + 2 * s) ^ (-c))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    have h := integrableOn_one_dim r hr
    rwa [show ((r : ℝ) + 2) / 2 = c from hc_def.symm] at h
  -- hence the product majorant is integrable
  have hB : Integrable (fun p : ℝ × ℝ => (1 - τ ^ 2) ^ (-c) *
      ((p.1 ^ (-(1/2) : ℝ) * (1 + 2 * p.1) ^ (-c)) *
        (p.2 ^ (-(1/2) : ℝ) * (1 + 2 * p.2) ^ (-c)))) planeMeasure := by
    have h := (hg.mul_prod hg).const_mul ((1 - τ ^ 2) ^ (-c))
    simpa [planeMeasure] using h
  -- almost every point of `planeMeasure` lies in the open quadrant
  have hae : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
    have h : ∀ᵐ p ∂planeMeasure, p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) := by
      rw [planeMeasure, Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [h] with p hp
    exact hp
  -- the kernel is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-c))
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    intro p hp
    have hp1 : (0:ℝ) < p.1 := hp.1
    have hp2 : (0:ℝ) < p.2 := hp.2
    have hst : (0:ℝ) < p.1 * p.2 := mul_pos hp1 hp2
    have h1s : (0:ℝ) < 1 + 2 * p.1 := by linarith
    have h1t : (0:ℝ) < 1 + 2 * p.2 := by linarith
    have hkey : (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2
        = (1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2) + τ ^ 2 * (1 + 2 * p.1 + 2 * p.2) := by
      ring
    have hKpos : (0:ℝ) < (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2 := by
      rw [hkey]
      have h1 : (0:ℝ) < (1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2) :=
        mul_pos (mul_pos ht2 h1s) h1t
      have h2 : (0:ℝ) ≤ τ ^ 2 * (1 + 2 * p.1 + 2 * p.2) :=
        mul_nonneg (sq_nonneg τ) (by linarith)
      linarith
    have hfst : ContinuousAt (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ)) p := by
      have hmul : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) p := by fun_prop
      have hrp : ContinuousAt (fun y : ℝ => y ^ (-(1/2) : ℝ)) (p.1 * p.2) :=
        Real.continuousAt_rpow_const (p.1 * p.2) (-(1/2)) (Or.inl hst.ne')
      exact hrp.comp (f := fun p : ℝ × ℝ => p.1 * p.2) hmul
    have hsnd : ContinuousAt (fun p : ℝ × ℝ =>
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-c)) p := by
      have hpoly : ContinuousAt (fun p : ℝ × ℝ =>
          (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) p := by fun_prop
      have hrp : ContinuousAt (fun y : ℝ => y ^ (-c))
          ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) :=
        Real.continuousAt_rpow_const _ _ (Or.inl hKpos.ne')
      exact hrp.comp (f := fun p : ℝ × ℝ =>
        (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) hpoly
    exact (hfst.mul hsnd).continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-c)) planeMeasure := by
    have hS : MeasurableSet (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
      measurableSet_Ioi.prod measurableSet_Ioi
    have h := hcont.aestronglyMeasurable (μ := volume) hS
    rw [planeMeasure, Measure.prod_restrict]
    exact h
  refine Integrable.mono' hB hmeas ?_
  filter_upwards [hae] with p hp
  have hp1 : (0:ℝ) < p.1 := hp.1
  have hp2 : (0:ℝ) < p.2 := hp.2
  have hst : (0:ℝ) < p.1 * p.2 := mul_pos hp1 hp2
  have h1s : (0:ℝ) < 1 + 2 * p.1 := by linarith
  have h1t : (0:ℝ) < 1 + 2 * p.2 := by linarith
  have hkey : (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2
      = (1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2) + τ ^ 2 * (1 + 2 * p.1 + 2 * p.2) := by
    ring
  have hApos : (0:ℝ) < (1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2) :=
    mul_pos (mul_pos ht2 h1s) h1t
  have hKge : (1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2) ≤
      (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2 := by
    rw [hkey]
    have h2 : (0:ℝ) ≤ τ ^ 2 * (1 + 2 * p.1 + 2 * p.2) :=
      mul_nonneg (sq_nonneg τ) (by linarith)
    linarith
  have hKpos : (0:ℝ) < (1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2 :=
    lt_of_lt_of_le hApos hKge
  have hpos1 : (0:ℝ) < (p.1 * p.2) ^ (-(1/2) : ℝ) := Real.rpow_pos_of_pos hst _
  have hpos2 : (0:ℝ) < ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-c) :=
    Real.rpow_pos_of_pos hKpos _
  have hpow_le : ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-c) ≤
      ((1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2)) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hApos hKge (neg_nonpos.mpr hc0.le)
  have hpow_split : ((1 - τ ^ 2) * (1 + 2 * p.1) * (1 + 2 * p.2)) ^ (-c)
      = (1 - τ ^ 2) ^ (-c) * ((1 + 2 * p.1) ^ (-c) * (1 + 2 * p.2) ^ (-c)) := by
    rw [Real.mul_rpow (le_of_lt (mul_pos ht2 h1s)) (le_of_lt h1t),
      Real.mul_rpow (le_of_lt ht2) (le_of_lt h1s)]
    ring
  have hst_split : (p.1 * p.2) ^ (-(1/2) : ℝ) =
      p.1 ^ (-(1/2) : ℝ) * p.2 ^ (-(1/2) : ℝ) :=
    Real.mul_rpow (le_of_lt hp1) (le_of_lt hp2)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hpos1 hpos2)]
  calc (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-c)
      ≤ (p.1 * p.2) ^ (-(1/2) : ℝ) *
          ((1 - τ ^ 2) ^ (-c) * ((1 + 2 * p.1) ^ (-c) * (1 + 2 * p.2) ^ (-c))) := by
        have h := mul_le_mul_of_nonneg_left hpow_le (le_of_lt hpos1)
        rwa [hpow_split] at h
    _ = (1 - τ ^ 2) ^ (-c) * ((p.1 ^ (-(1/2) : ℝ) * (1 + 2 * p.1) ^ (-c)) *
          (p.2 ^ (-(1/2) : ℝ) * (1 + 2 * p.2) ^ (-c))) := by
        rw [hst_split]; ring

end

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      planeMeasure :=
  integrable_kernel_proof r hr hτ
