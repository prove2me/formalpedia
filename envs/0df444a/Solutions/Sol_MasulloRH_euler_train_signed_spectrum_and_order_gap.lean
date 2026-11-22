-- Prove2me | solution 1 for MasulloRH.euler_train_signed_spectrum_and_order_gap
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T23:58:34.5405+00:00
-- url     : https://prove2.me/submissions/19dccf38-ecc7-49ed-b9b3-5c2945f5b114

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open InnerProductSpace
open scoped ComplexConjugate

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (u : ℂ) (hu : ‖u‖ = 1) :
    let H := lp (fun _ : ℕ => ℂ) 2
    let e : H := lp.single 2 0 1
    let c : ℂ := Real.sqrt (1-r^2)
    ∃ t : H, (∀ n : ℕ, t n = c * ((r : ℂ) * conj u)^n) ∧ ‖t‖ = 1 ∧
      let D := rankOne ℂ t t - rankOne ℂ e e
      let xp := c • t + ((r : ℂ) - 1) • e
      let xm := c • t + (-(r : ℂ) - 1) • e
      xp ≠ 0 ∧ xm ≠ 0 ∧ D xp = (r : ℂ) • xp ∧ D xm = -(r : ℂ) • xm ∧
        ‖D‖ = r ∧ ∀ B : H →L[ℂ] H, B.IsPositive → r ≤ ‖D - B‖ ∧ r ≤ ‖D + B‖ := by
  classical
  let H := lp (fun _ : ℕ => ℂ) 2
  let e : H := lp.single 2 0 1
  let c : ℝ := Real.sqrt (1 - r^2)
  let w (n : ℕ) : ℂ := c * ((r : ℂ) * conj u)^n
  have hq : r^2 < 1 := by nlinarith [mul_pos hr (sub_pos.mpr hr1), sq_nonneg (1-r)]
  have hc : 0 < c := Real.sqrt_pos.2 (sub_pos.mpr hq)
  have hc2 : c ^ 2 = 1 - r^2 := Real.sq_sqrt (by linarith)
  have hn (n : ℕ) : ‖w n‖ ^ 2 = (1 - r^2) * (r^2)^n := by
    simp [w, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
      abs_of_pos hr, hu, mul_pow, hc2, pow_right_comm r n 2]
  have hsum : HasSum (fun n => ‖w n‖^2) 1 := by
    simp_rw [hn]
    have g : HasSum (fun n : ℕ => (1-r^2)*(r^2)^n) ((1-r^2)*(1-r^2)⁻¹) :=
      (hasSum_geometric_of_lt_one (sq_nonneg r) hq).mul_left (1-r^2)
    rwa [mul_inv_cancel₀ (show (1:ℝ)-r^2 ≠ 0 by linarith)] at g
  have hw : Memℓp w 2 := memℓp_gen (by simpa using hsum.summable)
  let t : H := ⟨w, hw⟩
  have ht (n : ℕ) : t n = w n := rfl
  have ht1 : ‖t‖ = 1 := by
    have hs := lp.hasSum_norm (p := 2) (by norm_num) t
    have hsq : ‖t‖^2 = 1 := (by simpa [ht] using hs : HasSum (fun n => ‖w n‖^2) (‖t‖^2)).unique hsum
    nlinarith [norm_nonneg t]
  refine ⟨t, fun _ => rfl, ht1, ?_⟩
  let D : H →L[ℂ] H := rankOne ℂ t t - rankOne ℂ e e
  have et : inner ℂ e t = (c : ℂ) := calc
    _ = inner ℂ (1:ℂ) (t 0) := lp.inner_single_left (G := fun _ : ℕ => ℂ) (𝕜 := ℂ) 0 1 t
    _ = _ := by simp [ht, w]
  have te : inner ℂ t e = (c : ℂ) := calc
    _ = inner ℂ (t 0) (1:ℂ) := lp.inner_single_right (G := fun _ : ℕ => ℂ) (𝕜 := ℂ) 0 1 t
    _ = _ := by simp [ht, w]
  have ee : inner ℂ e e = 1 := calc
    _ = inner ℂ (1:ℂ) (e 0) := lp.inner_single_left (G := fun _ : ℕ => ℂ) (𝕜 := ℂ) 0 1 e
    _ = _ := by change inner ℂ (1:ℂ) (1:ℂ) = 1; simp
  have tt : inner ℂ t t = 1 := by simp [inner_self_eq_norm_sq_to_K, ht1]
  have Dt : D t = t - (c : ℂ) • e := by
    change inner ℂ t t • t - inner ℂ e t • e = _
    rw [tt, et, one_smul]
  have De : D e = (c : ℂ) • t - e := by
    change inner ℂ t e • t - inner ℂ e e • e = _
    rw [te, ee, one_smul]
  let x (s : ℂ) : H := (c : ℂ) • t + (s-1) • e
  have hne (s : ℂ) : x s ≠ 0 := by
    intro h
    have h1 := congrArg (fun z : H => z 1) h
    have hu0 : u ≠ 0 := by intro h0; simp [h0] at hu
    change (c:ℂ) * w 1 + (s - 1) * (0:ℂ) = 0 at h1
    simpa [w, hc.ne', hr.ne', hu0] using h1
  have hcc : (c : ℂ)^2 = 1 - (r : ℂ)^2 := by exact_mod_cast hc2
  have heig (s : ℂ) (hs : s^2 = (r : ℂ)^2) : D (x s) = s • x s := by
    simp only [x, map_add, map_smul, Dt, De]
    apply lp.ext
    funext n
    change (c:ℂ) * (t n - (c:ℂ)*e n) + (s-1)*((c:ℂ)*t n - e n) =
      s * ((c:ℂ)*t n + (s-1)*e n)
    linear_combination -(e n) * hcc - (e n) * hs
  have hp := heig (r : ℂ) rfl
  have hm := heig (-(r : ℂ)) (by ring)
  have hD3 (v : H) : D (D (D v)) = (r : ℂ)^2 • D v := by
    have hdv : D v = inner ℂ t v • t - inner ℂ e v • e := rfl
    rw [hdv]
    simp only [map_sub, map_smul, Dt, De]
    apply lp.ext
    funext n
    change (inner ℂ t v)*((t n-(c:ℂ)*e n) - (c:ℂ)*((c:ℂ)*t n-e n)) -
      (inner ℂ e v)*((c:ℂ)*(t n-(c:ℂ)*e n)-((c:ℂ)*t n-e n)) =
      (r:ℂ)^2 * ((inner ℂ t v)*t n - (inner ℂ e v)*e n)
    linear_combination ((inner ℂ e v) * (e n) - (inner ℂ t v) * (t n)) * hcc
  have h4 : D^4 = ((r:ℂ)^2) • (D^2) := by
    ext1 v
    simpa [pow_succ, ContinuousLinearMap.mul_apply] using hD3 (D v)
  have hsa : IsSelfAdjoint D := (isPositive_rankOne_self t).isSelfAdjoint.sub
    (isPositive_rankOne_self e).isSelfAdjoint
  have h2n : ‖D^2‖ = ‖D‖^2 := by simpa using hsa.norm_pow_two_pow 1
  have h4n : ‖D^4‖ = ‖D‖^4 := by simpa using hsa.norm_pow_two_pow 2
  rw [h4, norm_smul, h2n, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h4n
  have hDpos : 0 < ‖D‖ := by
    apply norm_pos_iff.mpr
    intro h0
    have hh : (r : ℂ) • x (r : ℂ) = 0 := hp.symm.trans (by simp [h0])
    exact (smul_ne_zero (by exact_mod_cast hr.ne') (hne _)) hh
  have hDnorm : ‖D‖ = r := by
    have hsq : r^2 = ‖D‖^2 := mul_right_cancel₀ (pow_ne_zero 2 hDpos.ne') (by nlinarith [h4n] : r^2 * ‖D‖^2 = ‖D‖^2 * ‖D‖^2)
    nlinarith
  refine ⟨hne _, hne _, hp, hm, hDnorm, ?_⟩
  intro B hB
  have gap (T : H →L[ℂ] H) (v : H) (hv : v ≠ 0) (hTv : T v = -(r : ℂ) • v) :
      r ≤ ‖T-B‖ := by
    have hb := hB.re_inner_nonneg_right v
    have hbnd : (inner ℂ v ((B-T) v)).re ≤ ‖B-T‖ * ‖v‖^2 := calc
      _ ≤ ‖v‖ * ‖(B-T) v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖v‖ * (‖B-T‖ * ‖v‖) := mul_le_mul_of_nonneg_left ((B-T).le_opNorm v) (norm_nonneg v)
      _ = ‖B-T‖ * ‖v‖^2 := by ring
    rw [ContinuousLinearMap.sub_apply, hTv, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K] at hbnd
    simp [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul] at hbnd hb
    rw [norm_sub_rev] at hbnd
    exact (le_of_mul_le_mul_right (by linarith : r * ‖v‖^2 ≤ ‖T-B‖ * ‖v‖^2)
      (sq_pos_of_pos (norm_pos_iff.mpr hv)))
  refine ⟨gap D _ (hne _) hm, ?_⟩
  have hh := gap (-D) _ (hne (r : ℂ)) (by simpa using congrArg Neg.neg hp)
  change r ≤ ‖D+B‖
  simpa only [sub_eq_add_neg, ← neg_add, norm_neg] using hh
