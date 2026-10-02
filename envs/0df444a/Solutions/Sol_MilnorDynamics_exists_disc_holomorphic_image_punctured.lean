-- Prove2me | solution 1 for MilnorDynamics.exists_disc_holomorphic_image_punctured
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:35:45.389057+00:00
-- url     : https://prove2.me/submissions/3d7ef853-22e8-4532-9068-89205177ecb3

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

set_option autoImplicit false

namespace D007452cAux

open Complex

/-- Cayley map from the unit disc onto the right half-plane. -/
noncomputable def cay (z : ℂ) : ℂ := (1 + z) / (1 - z)

/-- The explicit surjection: `exp (2πi · w²/(1+w²))` with `w = cay z`. -/
noncomputable def pmap (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((cay z) ^ 2 / (1 + (cay z) ^ 2)))

lemma one_sub_ne {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this] at hz; simp at hz

lemma cay_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (cay z).re := by
  have hne := one_sub_ne hz
  have hn : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  have h2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h3 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h3
    nlinarith
  unfold cay
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  rw [← add_div]
  apply div_pos _ hn
  nlinarith

lemma sq_ne_nonpos {w : ℂ} (hw : 0 < w.re) (r : ℝ) (hr : r ≤ 0) : w ^ 2 ≠ (r : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [pow_two, Complex.mul_re, Complex.ofReal_re] at hre
  rw [pow_two, Complex.mul_im, Complex.ofReal_im] at him
  have hb : w.im = 0 := by
    have h4 : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · exact h5
  rw [hb] at hre
  nlinarith

lemma one_add_sq_ne {w : ℂ} (hw : 0 < w.re) : 1 + w ^ 2 ≠ 0 := by
  intro h
  apply sq_ne_nonpos hw (-1) (by norm_num)
  push_cast
  linear_combination h

lemma pmap_diff : DifferentiableOn ℂ pmap (Metric.ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa using hz
  have h1 := one_sub_ne hz'
  have h2 := one_add_sq_ne (cay_re_pos hz')
  apply DifferentiableAt.differentiableWithinAt
  have hc : DifferentiableAt ℂ cay z := by
    unfold cay
    exact ((differentiableAt_const _).add differentiableAt_id).div
      ((differentiableAt_const _).sub differentiableAt_id) h1
  unfold pmap
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  exact (hc.pow 2).div ((differentiableAt_const _).add (hc.pow 2)) h2

lemma pmap_ne {z : ℂ} (hz : ‖z‖ < 1) : pmap z ≠ 0 ∧ pmap z ≠ 1 := by
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro h
  unfold pmap at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hw := cay_re_pos hz
  have h2 := one_add_sq_ne hw
  set w := cay z with hwdef
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hu : w ^ 2 / (1 + w ^ 2) = n := by
    have h6 := hn
    rw [mul_comm (n : ℂ)] at h6
    exact mul_left_cancel₀ hpi h6
  have hw2 : w ^ 2 * (1 - n) = n := by
    field_simp at hu
    linear_combination hu
  have hn1 : (n : ℂ) ≠ 1 := by
    intro h; rw [h] at hw2; simp at hw2
  have hn1' : n ≠ 1 := by intro h; apply hn1; simp [h]
  have hsub : (1 - (n : ℂ)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hn1)
  apply sq_ne_nonpos hw ((n : ℝ) / (1 - n)) ?_ ?_
  · rcases le_or_gt n 0 with h | h
    · have h7 : (n : ℝ) ≤ 0 := by exact_mod_cast h
      exact div_nonpos_iff.mpr (Or.inr ⟨h7, by linarith⟩)
    · have h8 : (2 : ℤ) ≤ n := by omega
      have h9 : (2 : ℝ) ≤ n := by exact_mod_cast h8
      exact div_nonpos_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
  · push_cast
    rw [eq_div_iff hsub]
    exact hw2

lemma inv_disc {w : ℂ} (hw : 0 < w.re) :
    ‖(w - 1) / (w + 1)‖ < 1 ∧ cay ((w - 1) / (w + 1)) = w := by
  have hw1 : w + 1 ≠ 0 := by
    intro h; have h2 := congrArg Complex.re h; simp at h2; linarith
  constructor
  · rw [norm_div, div_lt_one (norm_pos_iff.mpr hw1)]
    have h3 : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
        Complex.add_im, Complex.one_im]
      nlinarith
    nlinarith [norm_nonneg (w - 1), norm_nonneg (w + 1)]
  · unfold cay
    have e1 : 1 + (w - 1) / (w + 1) = 2 * w / (w + 1) := by
      field_simp; ring
    have e2 : 1 - (w - 1) / (w + 1) = 2 / (w + 1) := by
      field_simp; ring
    rw [e1, e2]
    field_simp

lemma sqrt_exists {s : ℂ} (hs : 0 < s.re ∨ s.im ≠ 0) : ∃ w : ℂ, 0 < w.re ∧ w ^ 2 = s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  refine ⟨Complex.exp (Complex.log s / 2), ?_, ?_⟩
  · rw [Complex.exp_re]
    apply mul_pos (Real.exp_pos _)
    apply Real.cos_pos_of_mem_Ioo
    have h1 := Complex.neg_pi_lt_arg s
    have h2 : Complex.arg s ≠ Real.pi := by
      rw [Ne, Complex.arg_eq_pi_iff]
      rintro ⟨h3, h4⟩
      rcases hs with h | h
      · linarith
      · exact h h4
    have h3 := Complex.arg_le_pi s
    have h4 : Complex.arg s < Real.pi := lt_of_le_of_ne h3 h2
    have h5 : (Complex.log s / 2).im = Complex.arg s / 2 := by
      simp [Complex.log_im]
    rw [h5]
    constructor <;> linarith
  · rw [← Complex.exp_nat_mul]
    have h6 : ((2 : ℕ) : ℂ) * (Complex.log s / 2) = Complex.log s := by push_cast; ring
    rw [h6, Complex.exp_log hs0]

lemma pmap_surj {ζ : ℂ} (h0 : ζ ≠ 0) (h1 : ζ ≠ 1) : ∃ z : ℂ, ‖z‖ < 1 ∧ pmap z = ζ := by
  have hpi := Real.pi_pos
  have harg1 := Complex.neg_pi_lt_arg ζ
  have harg2 := Complex.arg_le_pi ζ
  set θ : ℝ := if 0 < Complex.arg ζ then Complex.arg ζ else Complex.arg ζ + 2 * Real.pi
    with hθ
  have hθ0 : 0 < θ := by rw [hθ]; split_ifs with h <;> linarith
  have hθ1 : θ ≤ 2 * Real.pi := by rw [hθ]; split_ifs with h <;> linarith
  have hexp : Complex.exp (θ * Complex.I) = Complex.exp (Complex.arg ζ * Complex.I) := by
    rw [hθ]; split_ifs with h
    · rfl
    · push_cast
      rw [add_mul, Complex.exp_add]
      simp
  have hθ2 : θ = 2 * Real.pi → Real.log ‖ζ‖ ≠ 0 := by
    intro hθe hl
    have hn : ‖ζ‖ = 1 := Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr h0) hl
    have ha : Complex.arg ζ = 0 := by
      rw [hθ] at hθe; split_ifs at hθe with h <;> linarith
    apply h1
    have h3 := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hn, ha] at h3
    simpa using h3.symm
  set x : ℝ := θ / (2 * Real.pi) with hx
  set y : ℝ := -Real.log ‖ζ‖ / (2 * Real.pi) with hy
  set v : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hv
  have hvre : v.re = x := by simp [hv]
  have hvim : v.im = y := by simp [hv]
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by positivity)]; exact hθ1
  have hxy : x = 1 → y ≠ 0 := by
    intro h hy0
    apply hθ2
    · rw [hx, div_eq_one_iff_eq (by positivity)] at h; exact h
    · rw [hy] at hy0
      have h5 : -Real.log ‖ζ‖ = 0 := by
        rcases div_eq_zero_iff.mp hy0 with h6 | h6
        · exact h6
        · exfalso; linarith
      linarith
  -- exp (2πi v) = ζ
  have hkey : 2 * Real.pi * Complex.I * v = (Real.log ‖ζ‖ : ℂ) + θ * Complex.I := by
    have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hv, hx, hy]
    push_cast
    field_simp
    linear_combination (-((Real.log ‖ζ‖ : ℂ))) * Complex.I_sq
  have hev : Complex.exp (2 * Real.pi * Complex.I * v) = ζ := by
    rw [hkey, Complex.exp_add, hexp, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr h0)]
    exact Complex.norm_mul_exp_arg_mul_I ζ
  -- 1 - v ≠ 0
  have hv1 : 1 - v ≠ 0 := by
    intro h
    have h2 : v = 1 := by linear_combination -h
    have h3 : v.re = 1 := by rw [h2]; simp
    have h4 : v.im = 0 := by rw [h2]; simp
    rw [hvre] at h3; rw [hvim] at h4
    exact hxy h3 h4
  set s : ℂ := v / (1 - v) with hs
  have hN : 0 < Complex.normSq (1 - v) := Complex.normSq_pos.mpr hv1
  have hsgood : 0 < s.re ∨ s.im ≠ 0 := by
    by_cases hy0 : y = 0
    · left
      have hx1' : x < 1 := lt_of_le_of_ne hx1 (fun h => hxy h hy0)
      rw [hs, Complex.div_re]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hvre, hvim, hy0]
      rw [← add_div]
      apply div_pos _ hN
      nlinarith
    · right
      rw [hs, Complex.div_im]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hvre, hvim]
      rw [← sub_div]
      apply div_ne_zero _ (ne_of_gt hN)
      intro h
      apply hy0
      nlinarith
  obtain ⟨w, hw, hw2⟩ := sqrt_exists hsgood
  obtain ⟨hzn, hcz⟩ := inv_disc hw
  refine ⟨(w - 1) / (w + 1), hzn, ?_⟩
  unfold pmap
  rw [hcz, hw2]
  have e : s / (1 + s) = v := by
    have e1 : 1 + s = 1 / (1 - v) := by
      rw [hs]; field_simp; ring
    rw [e1, hs]
    field_simp
  rw [e, hev]

end D007452cAux

open MilnorDynamics Filter Set in
theorem solution :
    exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        p '' (Metric.ball 0 1) = {0, 1}ᶜ := by
  refine ⟨D007452cAux.pmap, D007452cAux.pmap_diff, ?_, ?_⟩
  · intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    obtain ⟨h0, h1⟩ := D007452cAux.pmap_ne hz'
    simp [h0, h1]
  · ext ζ
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : ‖z‖ < 1 := by simpa using hz
      obtain ⟨h0, h1⟩ := D007452cAux.pmap_ne hz'
      simp [h0, h1]
    · intro hζ
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hζ
      obtain ⟨z, hz, hpz⟩ := D007452cAux.pmap_surj hζ.1 hζ.2
      exact ⟨z, by simpa using hz, hpz⟩
