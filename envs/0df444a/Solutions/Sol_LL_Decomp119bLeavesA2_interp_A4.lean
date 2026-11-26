-- Prove2me | solution 1 for LL_Decomp119bLeavesA2.interp_A4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:29:55.755776+00:00
-- url     : https://prove2.me/submissions/962ec649-7e69-408f-add3-02c19de52f75

import Mathlib

open MeasureTheory Set Real
namespace LL_Decomp119bLeavesA2
theorem _root_.solution (g : ℝ → ℂ) (M a b : ℝ) (hab : a ≤ b) (hg : ContDiff ℝ 2 g)
    (hM : ∀ v ∈ Icc a b, ‖deriv (deriv g) v‖ ≤ M) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖g t‖ ≤ max ‖g a‖ ‖g b‖ + (b - a) ^ 2 / 8 * M := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have : t = a := le_antisymm ht.2 ht.1
    subst this; simp
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a ⟨le_rfl, hab⟩)
  set L : ℝ → ℂ := fun v => g a + (((v - a) / (b - a) : ℝ) : ℂ) * (g b - g a) with hL
  have hba : b - a ≠ 0 := (sub_pos.2 hlt).ne'
  have hLb : ‖L t‖ ≤ max ‖g a‖ ‖g b‖ := by
    set s : ℝ := (t - a) / (b - a) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) (by linarith)
    have hs1 : s ≤ 1 := (div_le_one (sub_pos.2 hlt)).2 (by linarith [ht.2])
    have e : L t = ((1 - s : ℝ) : ℂ) * g a + (s : ℂ) * g b := by
      simp only [hL, ← hs]; push_cast; ring
    rw [e]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0]
    nlinarith [le_max_left ‖g a‖ ‖g b‖, le_max_right ‖g a‖ ‖g b‖]
  have hh : ‖g t - L t‖ ≤ (b - a) ^ 2 / 8 * M := by
    obtain ⟨w, hw1, hw2⟩ : ∃ w : ℂ, ‖w‖ ≤ 1 ∧ (w * (g t - L t)).re = ‖g t - L t‖ := by
      by_cases h0 : g t - L t = 0
      · exact ⟨0, by simp, by simp [h0]⟩
      refine ⟨(starRingEnd ℂ (g t - L t)) / (‖g t - L t‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0)]
      · have hn : (‖g t - L t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
        have : starRingEnd ℂ (g t - L t) / (‖g t - L t‖ : ℂ) * (g t - L t) = (‖g t - L t‖ : ℂ) := by
          rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]; ring
        rw [this, Complex.ofReal_re]
    set T : ℂ →L[ℝ] ℝ := Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) w) with hT
    have hTa : ∀ z, T z = (w * z).re := fun z => rfl
    set k : ℂ := (g b - g a) * (((b - a)⁻¹ : ℝ) : ℂ) with hk
    have hLder : ∀ v, HasDerivAt L k v := by
      intro v
      have h1 : HasDerivAt (fun v : ℝ => (v - a) / (b - a)) ((b - a)⁻¹) v := by
        simpa [one_div] using ((hasDerivAt_id v).sub_const a).div_const (b - a)
      have h2 := (h1.ofReal_comp.mul_const (g b - g a)).const_add (g a)
      rw [hk, mul_comm]; exact h2
    have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
    have hg2 : Differentiable ℝ (deriv g) := by
      have : ContDiff ℝ (1 + 1) g := by rw [one_add_one_eq_two]; exact hg
      exact (contDiff_succ_iff_deriv.1 this).2.2.differentiable (by norm_num)
    set ψ : ℝ → ℝ := fun v => T (g v - L v) - M / 2 * ((v - a) * (b - v)) with hψ
    set ψ1 : ℝ → ℝ := fun v => T (deriv g v - k) - M / 2 * ((b - v) - (v - a)) with hψ1
    have d1 : ∀ v, HasDerivAt ψ (ψ1 v) v := by
      intro v
      have h1 := T.hasFDerivAt.comp_hasDerivAt v ((hg1 v).hasDerivAt.sub (hLder v))
      have h2 : HasDerivAt (fun v : ℝ => (v - a) * (b - v)) ((b - v) - (v - a)) v := by
        have := ((hasDerivAt_id v).sub_const a).mul ((hasDerivAt_const v b).sub (hasDerivAt_id v))
        refine this.congr_deriv ?_
        simp; ring
      exact h1.sub (h2.const_mul (M / 2))
    have d2 : ∀ v, HasDerivAt ψ1 (T (deriv (deriv g) v) + M) v := by
      intro v
      have h1 := T.hasFDerivAt.comp_hasDerivAt v ((hg2 v).hasDerivAt.sub_const k)
      have h2 : HasDerivAt (fun v : ℝ => (b - v) - (v - a)) (-2) v := by
        have := ((hasDerivAt_const v b).sub (hasDerivAt_id v)).sub ((hasDerivAt_id v).sub_const a)
        refine this.congr_deriv ?_
        norm_num
      have := h1.sub (h2.const_mul (M / 2))
      refine this.congr_deriv ?_
      ring
    have hconv : ConvexOn ℝ (Icc a b) ψ := by
      refine convexOn_of_hasDerivWithinAt2_nonneg (f' := ψ1) (f'' := fun v => T (deriv (deriv g) v) + M) (convex_Icc a b)
        (fun v _ => (d1 v).continuousAt.continuousWithinAt) (fun v _ => (d1 v).hasDerivWithinAt)
        (fun v _ => (d2 v).hasDerivWithinAt) (fun v hv => ?_)
      have hv' : v ∈ Icc a b := interior_subset hv
      have : |T (deriv (deriv g) v)| ≤ M := by
        rw [hTa]
        refine le_trans (Complex.abs_re_le_norm _) ?_
        rw [norm_mul]
        calc ‖w‖ * ‖deriv (deriv g) v‖ ≤ 1 * M := mul_le_mul hw1 (hM v hv') (norm_nonneg _) zero_le_one
          _ = M := one_mul M
      linarith [neg_le_of_abs_le this]
    have ha0 : ψ a = 0 := by
      have : L a = g a := by simp [hL]
      simp [hψ, this]
    have hb0 : ψ b = 0 := by
      have : L b = g b := by
        have e : ((b - a) / (b - a) : ℝ) = 1 := div_self hba
        simp only [hL, e, Complex.ofReal_one, one_mul]; ring
      simp [hψ, this]
    have hle : ψ t ≤ 0 := by
      have := hconv.le_on_segment (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) (z := t) (by rw [segment_eq_Icc hab]; exact ht)
      rwa [ha0, hb0, max_self] at this
    have hT' : T (g t - L t) = ‖g t - L t‖ := by rw [hTa]; exact hw2
    simp only [hψ, hT'] at hle
    have hprod : (t - a) * (b - t) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg ((t - a) - (b - t))]
    nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ M / 2)]
  have := norm_add_le (L t) (g t - L t)
  rw [add_sub_cancel] at this
  linarith

end LL_Decomp119bLeavesA2
