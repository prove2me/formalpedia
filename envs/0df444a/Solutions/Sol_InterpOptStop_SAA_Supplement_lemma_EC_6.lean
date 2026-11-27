-- Prove2me | solution 1 for InterpOptStop.SAA.Supplement.lemma_EC_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:14.176799+00:00
-- url     : https://prove2.me/submissions/e1e2e92e-d61c-44dc-8352-6477ea349adc

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy

open MeasureTheory ProbabilityTheory

open InterpOptStop
open InterpOptStop.SAA
open InterpOptStop.SAA.Supplement

/-- The local estimate applies to arbitrary laws, without any coupling restriction. -/
theorem solution {n : ℕ} (m : ℕ) (hm : 0 < m)
    (β L : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hL : 0 ≤ L)
    (g c : Cube n → ℝ) (hg : EuclideanLipschitz L g) (hc : EuclideanLipschitz L c)
    (ν ν' : Measure (Cube n)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : Fin n → Fin m) (hz : ∀ᵐ z ∂ν, InCell h z) (hz' : ∀ᵐ z ∂ν', InCell h z) :
    (∫ z, (max (g z) (β * c z) -
      max (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν')) ∂ν) ≤
        2 * L * Real.sqrt n / m := by
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm
          have hsqrt : 0 ≤ Real.sqrt n / m := by positivity
          have hcell : ∀ z : Cube n, InCell h z → ∀ i,
              ((h i).val : ℝ) ≤ m * z.val i ∧ (m : ℝ) * z.val i ≤ (h i).val + 1 := by
            intro z hzc i
            have h1 : ⌈(m : ℝ) * z.val i⌉₊ - 1 = (h i).val := congrFun hzc i
            have h0 : 0 ≤ (m : ℝ) * z.val i := mul_nonneg hmR.le (z.property i).1
            constructor
            · rcases Nat.eq_zero_or_pos (h i).val with h2 | h2
              · rw [h2]; simpa using h0
              · have h3 : (h i).val < ⌈(m : ℝ) * z.val i⌉₊ := by omega
                exact (Nat.lt_ceil.mp h3).le
            · have h3 : ⌈(m : ℝ) * z.val i⌉₊ ≤ (h i).val + 1 := by omega
              have h4 := Nat.ceil_le.mp h3
              push_cast at h4
              exact h4
          have hdist : ∀ z z' : Cube n, InCell h z → InCell h z' →
              euclidean z z' ≤ Real.sqrt n / m := by
            intro z z' h1 h2
            have hsum : ∑ i, (z.val i - z'.val i) ^ 2 ≤ (n : ℝ) / (m : ℝ) ^ 2 := by
              have : ∀ i ∈ (Finset.univ : Finset (Fin n)),
                  (z.val i - z'.val i) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
                intro i _
                obtain ⟨a1, a2⟩ := hcell z h1 i
                obtain ⟨b1, b2⟩ := hcell z' h2 i
                rw [le_div_iff₀ (by positivity)]
                have : (z.val i - z'.val i) ^ 2 * (m : ℝ) ^ 2
                    = (m * z.val i - m * z'.val i) ^ 2 := by ring
                rw [this]
                nlinarith
              refine (Finset.sum_le_sum this).trans ?_
              simp [div_eq_mul_inv]
            unfold euclidean
            refine (Real.sqrt_le_sqrt hsum).trans ?_
            rw [Real.sqrt_div (by positivity), Real.sqrt_sq hmR.le]
          have hcontE : ∀ z : Cube n, Continuous (fun y : Cube n => euclidean y z) := by
            intro z
            unfold euclidean
            refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
            exact (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).pow 2
          have hcont : ∀ f : Cube n → ℝ, EuclideanLipschitz L f → Continuous f := by
            intro f hf
            rw [continuous_iff_continuousAt]
            intro z
            have hlim : Filter.Tendsto (fun y : Cube n => L * euclidean y z) (nhds z) (nhds 0) := by
              have := ((hcontE z).const_mul L).tendsto z
              simpa [euclidean] using this
            refine tendsto_iff_dist_tendsto_zero.mpr ?_
            refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hlim
            rw [Real.dist_eq]
            exact hf y z
          have hmean : ∀ f : Cube n → ℝ, EuclideanLipschitz L f → ∀ z, InCell h z →
              f z - ∫ z', f z' ∂ν' ≤ L * (Real.sqrt n / m) := by
            intro f hf z hzc
            have hb : ∀ᵐ z' ∂ν', |f z - f z'| ≤ L * (Real.sqrt n / m) := by
              filter_upwards [hz'] with z' hzc'
              exact (hf z z').trans (mul_le_mul_of_nonneg_left (hdist z z' hzc hzc') hL)
            have hint : Integrable f ν' := by
              refine Integrable.of_bound (hcont f hf).aestronglyMeasurable
                (|f z| + L * (Real.sqrt n / m)) ?_
              filter_upwards [hb] with z' hz1
              rw [Real.norm_eq_abs]
              have h2 := abs_sub_abs_le_abs_sub (f z') (f z)
              rw [abs_sub_comm] at h2
              linarith
            have h3 : ∫ _z', (f z - L * (Real.sqrt n / m)) ∂ν' ≤ ∫ z', f z' ∂ν' := by
              refine integral_mono_ae (integrable_const _) hint ?_
              filter_upwards [hb] with z' hz1
              have := (abs_le.mp hz1).2
              linarith
            simp at h3
            linarith
          have hC : 0 ≤ L * (Real.sqrt n / m) := mul_nonneg hL hsqrt
          have hfinal : L * (Real.sqrt n / m) ≤ 2 * L * Real.sqrt n / m := by
            have : 2 * L * Real.sqrt n / m = 2 * (L * (Real.sqrt n / m)) := by ring
            rw [this]; linarith
          have hpt : ∀ᵐ z ∂ν, max (g z) (β * c z) -
              max (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν') ≤ L * (Real.sqrt n / m) := by
            filter_upwards [hz] with z hzc
            have h1 := hmean g hg z hzc
            have h2 := hmean c hc z hzc
            have h3 : ∫ z', β * c z' ∂ν' = β * ∫ z', c z' ∂ν' := integral_const_mul _ _
            have h4 : β * c z - ∫ z', β * c z' ∂ν' ≤ L * (Real.sqrt n / m) := by
              rw [h3]
              nlinarith [mul_le_mul_of_nonneg_left h2 hβ0, mul_le_mul_of_nonneg_right hβ1 hC]
            have h5 := le_max_left (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν')
            have h6 := le_max_right (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν')
            have h7 : max (g z) (β * c z) ≤
                max (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν') + L * (Real.sqrt n / m) :=
              max_le (by linarith) (by linarith)
            linarith
          refine le_trans ?_ hfinal
          by_cases hI : Integrable (fun z => max (g z) (β * c z) -
              max (∫ z', g z' ∂ν') (∫ z', β * c z' ∂ν')) ν
          · have := integral_mono_ae hI (integrable_const (L * (Real.sqrt n / m))) hpt
            simpa using this
          · rw [integral_undef hI]
            exact hC
