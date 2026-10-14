-- Prove2me | solution 1 for IntMul.HvdH.Sapprox_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T23:47:48.598393+00:00
-- url     : https://prove2.me/submissions/be61fe4a-cb5e-4c18-bb97-f47cec1ce990

import Definitions.Def_IntMul_HvdH_SApprox
import Theorems.Thm_IntMul_HvdH_expNeg_bound

open Complex

namespace IntMul.HvdH.SPf
open IntMul.HvdH

/-- A pair of integers as a Gaussian integer in `ℂ`. -/
def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

@[simp] lemma toC_re (p : ℤ × ℤ) : (toC p).re = p.1 := by simp [toC]
@[simp] lemma toC_im (p : ℤ × ℤ) : (toC p).im = p.2 := by simp [toC]

lemma norm_le_of_re_im {z : ℂ} {c : ℝ} (hre : |z.re| ≤ c) (him : |z.im| ≤ c) :
    ‖z‖ ≤ 3 / 2 * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hre
  have h1 : z.re ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 : z.im ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have : ‖z‖ ^ 2 ≤ (3 / 2 * c) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma tdiv_err (m D : ℤ) (hD : 0 < D) : |((m.tdiv D : ℤ) : ℝ) - (m : ℝ) / D| ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 := Int.tmod_lt_of_pos m hD
  have h2 := Int.lt_tmod_of_pos m hD
  rw [Int.tmod_def] at h1 h2
  have h1' : (m : ℝ) - D * (m.tdiv D : ℤ) < D := by exact_mod_cast h1
  have h2' : -(D : ℝ) < m - D * (m.tdiv D : ℤ) := by exact_mod_cast h2
  have e : ((m.tdiv D : ℤ) : ℝ) - (m : ℝ) / D = -((m - D * (m.tdiv D : ℤ)) / D) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hD', div_le_one hD', abs_le]
  constructor <;> linarith

lemma natdiv_bound (m n : ℕ) (hn : 0 < n) : |((m / n : ℕ) : ℝ) - (m : ℝ) / n| ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((m / n : ℕ) : ℝ) * n ≤ m := by exact_mod_cast Nat.div_mul_le_self m n
  have h2 : (m : ℝ) < ((m / n : ℕ) + 1 : ℝ) * n := by
    have := Nat.lt_mul_div_succ m hn
    have : (m : ℝ) < (n : ℝ) * ((m / n : ℕ) + 1 : ℝ) := by exact_mod_cast this
    linarith
  have h3 : (m : ℝ) / n < (m / n : ℕ) + 1 := by rw [div_lt_iff₀ hn']; linarith
  have h4 : ((m / n : ℕ) : ℝ) ≤ m / n := by rw [le_div_iff₀ hn']; linarith
  rw [abs_le]; constructor <;> linarith

/-- The exact weight `e_j = e^{-π (j - sk/t)² / α²}`. -/
noncomputable def ew (s t α k : ℕ) (j : ℤ) : ℝ := Real.exp (-(Real.pi * (j - (s * k : ℝ) / t) ^ 2 / α ^ 2))

lemma ew_le_one (s t α k : ℕ) (j : ℤ) : ew s t α k j ≤ 1 := by
  unfold ew; rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.pi * (j - (s * k : ℝ) / t) ^ 2 / α ^ 2 := by positivity
  linarith

/-- Per-term error: `‖sTerm j - 2^p β e_j u_j‖ ≤ 11/4` (in units of `2^{-p}`). -/
lemma sTerm_err (p s t α k : ℕ) (ht : 0 < t) (hα : 2 ≤ α) (U : ℕ → ℤ × ℤ)
    (hU : ∀ i, ‖toC (U i)‖ ≤ 2 ^ p) (j : ℤ) :
    ‖toC (sTerm p s t α k U j) -
      2 ^ p * ((((2 * α : ℝ)⁻¹ * ew s t α k j : ℝ) : ℂ) * (toC (U (j % s).toNat) / 2 ^ p))‖
      ≤ 11 / 4 := by
  set V := U (j % s).toNat
  set e := ew s t α k j
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := ew_le_one s t α k j
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hαR : (2 : ℝ) ≤ α := by exact_mod_cast hα
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  -- the exponential
  set J : ℕ := (t * j - s * k : ℤ).natAbs ^ 2
  have hx := expNeg_bound p (α ^ 2 * t ^ 2) J (by positivity)
  have hJ : Real.pi * (J : ℝ) / ((α ^ 2 * t ^ 2 : ℕ) : ℝ) = Real.pi * (j - (s * k : ℝ) / t) ^ 2 / α ^ 2 := by
    simp only [J]
    rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    push_cast; field_simp
  rw [hJ] at hx
  set x := expNeg p (α ^ 2 * t ^ 2) J
  have hx' : |(x : ℝ) - 2 ^ p * e| ≤ 1 := hx
  -- β
  have hb := natdiv_bound (2 ^ p) (2 * α) (by omega)
  set b : ℤ := betaT p α
  have hbR : (b : ℝ) = ((2 ^ p / (2 * α) : ℕ) : ℝ) := Int.cast_natCast _
  have hb0 : (0 : ℝ) ≤ b := by rw [hbR]; positivity
  have hbq : (2 ^ p : ℝ) / (2 * α) ≤ 2 ^ p / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hb' : |(b : ℝ) - 2 ^ p * (2 * α : ℝ)⁻¹| ≤ 1 := by
    rw [hbR]; push_cast at hb ⊢; rw [← div_eq_mul_inv]; exact hb
  have hbu : (b : ℝ) ≤ 2 ^ p / 4 := by
    rw [hbR]
    have : ((2 ^ p / (2 * α) : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) / ((2 * α : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at this; linarith
  -- w ≈ 2^{2p} β e
  set w : ℤ := b * x
  have hw : |(w : ℝ) - 2 ^ (2 * p) * ((2 * α : ℝ)⁻¹ * e)| ≤ 5 / 4 * 2 ^ p := by
    have e1 : (w : ℝ) - 2 ^ (2 * p) * ((2 * α : ℝ)⁻¹ * e)
        = (b : ℝ) * ((x : ℝ) - 2 ^ p * e) + 2 ^ p * e * ((b : ℝ) - 2 ^ p * (2 * α : ℝ)⁻¹) := by
      simp only [w]; push_cast; ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p * e)]
    have a1 : (b : ℝ) * |(x : ℝ) - 2 ^ p * e| ≤ 2 ^ p / 4 * 1 :=
      mul_le_mul hbu hx' (abs_nonneg _) (by positivity)
    have a2 : 2 ^ p * e * |(b : ℝ) - 2 ^ p * (2 * α : ℝ)⁻¹| ≤ 2 ^ p * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left he1 hp.le) hb' (abs_nonneg _) (by positivity)
    linarith
  -- rounding
  have hpZ : (0 : ℤ) < 2 ^ (2 * p) := by positivity
  have hp2 : (0 : ℝ) < 2 ^ (2 * p) := by positivity
  have hround : ‖toC (sTerm p s t α k U j) - (w : ℂ) * toC V / 2 ^ (2 * p)‖ ≤ 3 / 2 := by
    have hsC : (((2 ^ (2 * p) : ℤ) : ℝ) : ℂ) = (2 : ℂ) ^ (2 * p) := by push_cast; rfl
    refine (norm_le_of_re_im (c := 1) ?_ ?_).trans (by norm_num)
    · rw [← hsC, Complex.sub_re, Complex.div_ofReal_re, toC_re]
      have h := tdiv_err (w * V.1) (2 ^ (2 * p)) hpZ
      convert h using 2
      simp [toC]
      rfl
    · rw [← hsC, Complex.sub_im, Complex.div_ofReal_im, toC_im]
      have h := tdiv_err (w * V.2) (2 ^ (2 * p)) hpZ
      convert h using 2
      simp [toC]
      rfl
  have happ : ‖(w : ℂ) * toC V / 2 ^ (2 * p) -
      2 ^ p * ((((2 * α : ℝ)⁻¹ * e : ℝ) : ℂ) * (toC V / 2 ^ p))‖ ≤ 5 / 4 := by
    have e2 : (w : ℂ) * toC V / 2 ^ (2 * p) - 2 ^ p * ((((2 * α : ℝ)⁻¹ * e : ℝ) : ℂ) * (toC V / 2 ^ p))
        = ((((w : ℝ) - 2 ^ (2 * p) * ((2 * α : ℝ)⁻¹ * e)) / 2 ^ (2 * p) : ℝ) : ℂ) * toC V := by
      have : (2 : ℂ) ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [← pow_add]; ring_nf
      push_cast; rw [this]; field_simp
    rw [e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hp2]
    have : (2 : ℝ) ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [← pow_add]; ring_nf
    calc |(w : ℝ) - 2 ^ (2 * p) * ((2 * α : ℝ)⁻¹ * e)| / 2 ^ (2 * p) * ‖toC V‖
        ≤ 5 / 4 * 2 ^ p / 2 ^ (2 * p) * 2 ^ p :=
          mul_le_mul (div_le_div_of_nonneg_right hw hp2.le) (hU _) (norm_nonneg _) (by positivity)
      _ = 5 / 4 := by rw [this]; field_simp
  calc _ ≤ ‖toC (sTerm p s t α k U j) - (w : ℂ) * toC V / 2 ^ (2 * p)‖
        + ‖(w : ℂ) * toC V / 2 ^ (2 * p) -
          2 ^ p * ((((2 * α : ℝ)⁻¹ * e : ℝ) : ℂ) * (toC V / 2 ^ p))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 / 2 + 5 / 4 := add_le_add hround happ
    _ = 11 / 4 := by norm_num
lemma summable_gauss {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : c ≠ 0) (b : ℝ) :
    Summable (fun j : ℤ => Real.exp (-a * (c * j - b) ^ 2)) := by
  have hτ : 0 < (I * ((a * c ^ 2 / Real.pi : ℝ) : ℂ)).im := by
    have : 0 < c ^ 2 := by positivity
    rw [mul_im, I_re, I_im, ofReal_re, ofReal_im]
    simp only [zero_mul, one_mul, zero_add]
    positivity
  have h := ((summable_jacobiTheta₂_term_iff (I * ((-a * c * b / Real.pi : ℝ) : ℂ))
    (I * ((a * c ^ 2 / Real.pi : ℝ) : ℂ))).mpr hτ).norm
  have h2 := h.mul_left (Real.exp (-a * b ^ 2))
  refine h2.congr (fun n => ?_)
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im]
  field_simp
  ring

lemma hasSum_geom_int {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 + r) / (1 - r)) := by
  have h1 : HasSum (fun n : ℕ => r ^ ((n : ℤ).natAbs)) (1 / (1 - r)) := by
    simpa [one_div] using hasSum_geometric_of_lt_one hr0 hr1
  have h2 : HasSum (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) (r / (1 - r)) := by
    have e : (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) = fun n : ℕ => r * r ^ n := by
      funext n; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ, mul_comm]
    rw [e, div_eq_mul_inv]; exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have : 1 - r ≠ 0 := by linarith
  rw [show (1 + r) / (1 - r) = 1 / (1 - r) + r / (1 - r) by field_simp]
  exact h1.of_nat_of_neg_add_one h2

lemma exp_neg_pi_half_le : Real.exp (-Real.pi / 2) ≤ 1 / 4.3 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := Real.pi / 4) (by positivity)
  have e : Real.exp (Real.pi / 2) = Real.exp (Real.pi / 4) * Real.exp (Real.pi / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq : 2.09 ≤ Real.exp (Real.pi / 4) := by nlinarith
  have h2 : 4.3 ≤ Real.exp (Real.pi / 2) := by rw [e]; nlinarith
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.exp_neg, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith


lemma ceilSqrt_sq (p : ℕ) : p ≤ ceilSqrt p * ceilSqrt p := by
  unfold ceilSqrt
  split_ifs with h
  · exact (Nat.lt_succ_sqrt p).le
  · push Not at h; exact h

lemma ceilSqrt_ge (p α : ℕ) (h : α ^ 2 ≤ p) : α ≤ ceilSqrt p := by
  have := ceilSqrt_sq p
  by_contra hc; push Not at hc
  have : ceilSqrt p * ceilSqrt p < α * α := Nat.mul_lt_mul'' hc hc
  nlinarith

lemma ceil_bounds (s t k : ℕ) (ht : 0 < t) :
    let c : ℤ := ((s * k + t - 1) / t : ℕ)
    (c : ℝ) - 1 < (s * k : ℝ) / t ∧ (s * k : ℝ) / t ≤ c := by
  intro c
  set q := (s * k + t - 1) / t
  have h1 : q * t ≤ s * k + t - 1 := Nat.div_mul_le_self _ _
  have h2 : s * k + t - 1 < (q + 1) * t := by
    calc s * k + t - 1 < t * (q + 1) := Nat.lt_mul_div_succ _ ht
      _ = (q + 1) * t := by ring
  have h3 : s * k ≤ q * t := by
    rcases Nat.eq_zero_or_pos (s * k) with h | h
    · rw [h]; exact Nat.zero_le _
    · rw [add_mul, one_mul] at h2
      generalize q * t = P at h2 ⊢
      generalize s * k = S at h2 h ⊢
      omega
  have h4 : q * t < s * k + t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have h3' : (s * k : ℝ) ≤ q * t := by exact_mod_cast h3
  have h4' : (q : ℝ) * t < s * k + t := by exact_mod_cast h4
  have hc : (c : ℝ) = q := Int.cast_natCast q
  rw [hc]; constructor
  · rw [lt_div_iff₀ htR]; nlinarith
  · rw [div_le_iff₀ htR]; linarith

/-- The tail weight bound: outside the window, `e_j ≤ r^{m-1} r^{|j - c|}`. -/
lemma ew_tail (s t α k m : ℕ) (hα : 0 < α) (hm : 1 ≤ m) (c : ℤ) (hc1 : (c : ℝ) - 1 < (s * k : ℝ) / t)
    (hc2 : (s * k : ℝ) / t ≤ c) (j : ℤ) (hj : m + 1 ≤ (j - c).natAbs) :
    ew s t α k j ≤ Real.exp (-(Real.pi * m / (2 * α ^ 2))) ^ (m - 1) *
      Real.exp (-(Real.pi * m / (2 * α ^ 2))) ^ (j - c).natAbs := by
  set n := (j - c).natAbs
  set r := Real.exp (-(Real.pi * m / (2 * α ^ 2)))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ Real.pi * m / (2 * α ^ 2) := by positivity
    linarith
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have hn : (n : ℝ) = |(j : ℝ) - c| := by
    simp only [n]; rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
  have hnm : (m : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have hja : (n : ℝ) - 1 ≤ |(j : ℝ) - (s * k : ℝ) / t| := by
    rw [hn]
    have := abs_sub_abs_le_abs_sub ((j : ℝ) - c) ((j : ℝ) - (s * k : ℝ) / t)
    have hca : |((j : ℝ) - c) - ((j : ℝ) - (s * k : ℝ) / t)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  have hsq : (m : ℝ) * (n - 1) ≤ ((j : ℝ) - (s * k : ℝ) / t) ^ 2 := by
    have h0 : (0 : ℝ) ≤ n - 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have : ((n : ℝ) - 1) ^ 2 ≤ ((j : ℝ) - (s * k : ℝ) / t) ^ 2 := by
      rw [← sq_abs ((j : ℝ) - _)]; exact pow_le_pow_left₀ h0 hja 2
    nlinarith
  have hstep : ew s t α k j ≤ r ^ (2 * (n - 1)) := by
    unfold ew
    rw [show r ^ (2 * (n - 1)) = Real.exp (((2 * (n - 1) : ℕ) : ℝ) * (-(Real.pi * m / (2 * α ^ 2)))) by
      rw [Real.exp_nat_mul]]
    apply Real.exp_le_exp.2
    have hn1 : ((2 * (n - 1) : ℕ) : ℝ) = 2 * ((n : ℝ) - 1) := by
      have : 1 ≤ n := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [hn1]
    have hα2 : (0 : ℝ) < α ^ 2 := by positivity
    rw [neg_le_neg_iff.symm.trans (by rfl : _ ↔ _)]
    have : Real.pi * m * ((n : ℝ) - 1) / α ^ 2 ≤ Real.pi * ((j : ℝ) - (s * k : ℝ) / t) ^ 2 / α ^ 2 := by
      apply div_le_div_of_nonneg_right _ hα2.le
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    have e : 2 * ((n : ℝ) - 1) * -(Real.pi * m / (2 * α ^ 2)) = -(Real.pi * m * ((n : ℝ) - 1) / α ^ 2) := by
      field_simp
    rw [e]; linarith
  calc ew s t α k j ≤ r ^ (2 * (n - 1)) := hstep
    _ ≤ r ^ ((m - 1) + n) :=
        pow_le_pow_of_le_one hr0 hr1 (show (m - 1) + n ≤ 2 * (n - 1) by omega)
    _ = r ^ (m - 1) * r ^ n := pow_add _ _ _

lemma exp_neg_pi_quarter_le : Real.exp (-(Real.pi / 4)) ≤ 1 / 2 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := Real.pi / 4) (by positivity)
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  nlinarith

/-- Lemma 4.9: the truncated fixed-point sum approximates `2^p (S' u)_k` within `6m + 4`. -/
theorem Sapprox_bound (p s t α k : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖toC (U i)‖ ≤ 2 ^ p) :
    ‖toC (Sapprox p s t α U k) - 2 ^ p * Sexact s t α (fun i => toC (U i) / 2 ^ p) k‖
      ≤ 6 * sWidth p α + 4 := by
  set m := sWidth p α with hmdef
  set q := ceilSqrt p
  have hq : α ≤ q := ceilSqrt_ge p α hαp
  have hqp : p ≤ q * q := ceilSqrt_sq p
  have hm1 : 1 ≤ m := by simp only [hmdef, sWidth]; nlinarith
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hαR : (2 : ℝ) ≤ α := by exact_mod_cast hα
  have hα0 : (0 : ℝ) < α := by linarith
  set c : ℤ := (((s * k + t - 1) / t : ℕ) : ℤ) with hcdef
  obtain ⟨hc1, hc2⟩ := ceil_bounds s t k ht
  set u : ℕ → ℂ := fun i => toC (U i) / 2 ^ p
  have hu : ∀ i, ‖u i‖ ≤ 1 := by
    intro i; simp only [u]; rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hU i
  set g : ℤ → ℂ := fun j => (((2 * α : ℝ)⁻¹ * ew s t α k j : ℝ) : ℂ) * u (j % s).toNat with hg
  have hgS : Sexact s t α u k = ∑' j, g j := rfl
  -- summability
  have hgsum : Summable g := by
    have hsg := summable_gauss (a := Real.pi / α ^ 2) (by positivity) 1 one_ne_zero ((s * k : ℝ) / t)
    refine Summable.of_norm_bounded (hsg.mul_left (2 * α : ℝ)⁻¹) (fun j => ?_)
    simp only [hg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold ew; positivity)]
    have : ew s t α k j = Real.exp (-(Real.pi / α ^ 2) * (1 * (j : ℝ) - (s * k : ℝ) / t) ^ 2) := by
      unfold ew; congr 1; ring
    rw [this]
    calc (2 * α : ℝ)⁻¹ * Real.exp (-(Real.pi / α ^ 2) * (1 * (j : ℝ) - (s * k : ℝ) / t) ^ 2) * ‖u (j % s).toNat‖
        ≤ (2 * α : ℝ)⁻¹ * Real.exp (-(Real.pi / α ^ 2) * (1 * (j : ℝ) - (s * k : ℝ) / t) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (hu _) (by positivity)
      _ = _ := mul_one _
  -- the window
  set W : Finset ℤ := (Finset.range (2 * m + 1)).map
    ⟨fun i : ℕ => c - m + i, fun a b h => by simpa using h⟩ with hW
  have hWmem : ∀ j, j ∉ W → m + 1 ≤ (j - c).natAbs := by
    intro j hj
    by_contra hcon; push Not at hcon
    apply hj
    rw [hW, Finset.mem_map]
    refine ⟨(j - (c - m)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · show c - m + (((j - (c - m)).toNat : ℕ) : ℤ) = j; omega
  have halg : toC (Sapprox p s t α U k) = ∑ j ∈ W, toC (sTerm p s t α k U j) := by
    rw [hW, Finset.sum_map]
    simp only [Sapprox, toC, Int.cast_sum, Function.Embedding.coeFn_mk]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  rw [hgS, halg, ← hgsum.sum_add_tsum_compl (s := W), mul_add, Finset.mul_sum]
  have hsplit : ∑ j ∈ W, toC (sTerm p s t α k U j) - (∑ j ∈ W, 2 ^ p * g j + 2 ^ p * ∑' x : ↑(↑W : Set ℤ)ᶜ, g x)
      = ∑ j ∈ W, (toC (sTerm p s t α k U j) - 2 ^ p * g j) - 2 ^ p * ∑' x : ↑(↑W : Set ℤ)ᶜ, g x := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  -- window part
  have hwin : ‖∑ j ∈ W, (toC (sTerm p s t α k U j) - 2 ^ p * g j)‖ ≤ (2 * m + 1) * (11 / 4) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ W, ‖toC (sTerm p s t α k U j) - 2 ^ p * g j‖ ≤ ∑ _j ∈ W, (11 / 4 : ℝ) :=
          Finset.sum_le_sum (fun j _ => sTerm_err p s t α k ht hα U hU j)
      _ = (2 * m + 1) * (11 / 4) := by
          rw [Finset.sum_const, hW, Finset.card_map, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  -- tail part
  set r : ℝ := Real.exp (-(Real.pi * m / (2 * α ^ 2))) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrq : r ≤ 1 / 4.3 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_pi_half_le
    have hmR : (m : ℝ) = q * α := by simp [hmdef, sWidth, q]
    have hqR : (α : ℝ) ≤ q := by exact_mod_cast hq
    rw [hmR, show Real.pi * (q * α : ℝ) / (2 * α ^ 2) = Real.pi / 2 * (q / α) by field_simp]
    have : (1 : ℝ) ≤ q / α := by rw [le_div_iff₀ hα0]; linarith
    nlinarith [Real.pi_pos]
  have hr1 : r < 1 := by linarith
  set h : ℤ → ℝ := fun j => (2 * α : ℝ)⁻¹ * (r ^ (m - 1) * r ^ (j - c).natAbs) with hh
  have hhas : HasSum h ((2 * α : ℝ)⁻¹ * (r ^ (m - 1) * ((1 + r) / (1 - r)))) := by
    have h0 := hasSum_geom_int hr0 hr1
    have h1 : HasSum (fun j : ℤ => r ^ (j - c).natAbs) ((1 + r) / (1 - r)) := by
      rw [← (Equiv.subRight c).hasSum_iff] at h0
      · exact h0
    exact (h1.mul_left (r ^ (m - 1))).mul_left _
  have htail : ‖∑' x : ↑(↑W : Set ℤ)ᶜ, g x‖ ≤ (2 * α : ℝ)⁻¹ * (r ^ (m - 1) * ((1 + r) / (1 - r))) := by
    rw [tsum_subtype (↑W : Set ℤ)ᶜ g]
    refine tsum_of_norm_bounded hhas (fun j => ?_)
    by_cases hj : j ∈ (↑W : Set ℤ)ᶜ
    · rw [Set.indicator_of_mem hj]
      have hjW : j ∉ W := by simpa using hj
      have hb := ew_tail s t α k m (by omega) hm1 c hc1 hc2 j (hWmem j hjW)
      simp only [hg, hh]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold ew; positivity)]
      calc (2 * α : ℝ)⁻¹ * ew s t α k j * ‖u (j % s).toNat‖ ≤ (2 * α : ℝ)⁻¹ * ew s t α k j * 1 :=
            mul_le_mul_of_nonneg_left (hu _) (by unfold ew; positivity)
        _ ≤ (2 * α : ℝ)⁻¹ * (r ^ (m - 1) * r ^ (j - c).natAbs) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hb (by positivity)
    · rw [Set.indicator_of_notMem hj, norm_zero]; simp only [hh]; positivity
  -- numerics: 2^p * tail ≤ 1/2
  have hrm : (2 : ℝ) ^ p * r ^ (m - 1) ≤ 1 := by
    have e1 : r ^ (m - 1) = Real.exp (((m - 1 : ℕ) : ℝ) * (-(Real.pi * m / (2 * α ^ 2)))) := by
      rw [Real.exp_nat_mul]
    have e2 : (2 : ℝ) ^ p = Real.exp (p * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    rw [e1, e2, ← Real.exp_add, Real.exp_le_one_iff]
    have hmR : (m : ℝ) = q * α := by simp [hmdef, sWidth, q]
    have hm1R : ((m - 1 : ℕ) : ℝ) = q * α - 1 := by rw [Nat.cast_sub hm1, hmR]; simp
    rw [hm1R, hmR]
    have hqR : (α : ℝ) ≤ q := by exact_mod_cast hq
    have hqpR : (p : ℝ) ≤ q * q := by exact_mod_cast hqp
    have hl := Real.log_two_lt_d9
    have hpi := Real.pi_gt_d2
    -- (qα - 1) qα / (2α²) = (q² - q/α)/2 ≥ q²/4 ≥ p/4
    have key : (q * α - 1) * (Real.pi * (q * α) / (2 * α ^ 2)) = Real.pi / 2 * (q * q - q / α) := by
      field_simp
    have hqa : (q : ℝ) / α ≤ q / 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hαR
    have hq1 : (1 : ℝ) ≤ q := by linarith
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h1 : (p : ℝ) / 2 ≤ q * q - q / α := by nlinarith
    have h2 : Real.pi / 2 * ((p : ℝ) / 2) ≤ Real.pi / 2 * (q * q - q / α) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 3.14 * (p : ℝ) ≤ Real.pi * p := mul_le_mul_of_nonneg_right hpi.le hp0
    have : (p : ℝ) * 0.6931471808 ≤ Real.pi / 2 * (q * q - q / α) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hl.le hp0]
  have hgeo : (1 + r) / (1 - r) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hα4 : (2 * α : ℝ)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have htail2 : ‖(2 : ℂ) ^ p * ∑' x : ↑(↑W : Set ℤ)ᶜ, g x‖ ≤ 1 / 2 := by
    rw [norm_mul, norm_pow, Complex.norm_two]
    calc (2 : ℝ) ^ p * ‖∑' x : ↑(↑W : Set ℤ)ᶜ, g x‖
        ≤ 2 ^ p * ((2 * α : ℝ)⁻¹ * (r ^ (m - 1) * ((1 + r) / (1 - r)))) :=
          mul_le_mul_of_nonneg_left htail hp.le
      _ = (2 * α : ℝ)⁻¹ * ((2 ^ p * r ^ (m - 1)) * ((1 + r) / (1 - r))) := by ring
      _ ≤ 1 / 4 * (1 * 2) := by
          apply mul_le_mul hα4 _ (by positivity) (by norm_num)
          exact mul_le_mul hrm hgeo (by positivity) (by norm_num)
      _ = 1 / 2 := by norm_num
  have : ((2 * m + 1 : ℕ) : ℝ) = 2 * m + 1 := by push_cast; ring
  linarith

end IntMul.HvdH.SPf

open IntMul.HvdH in
theorem solution (p s t α k : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) :
    ‖(((Sapprox p s t α U k).1 : ℂ) + ((Sapprox p s t α U k).2 : ℂ) * Complex.I) -
      2 ^ p * Sexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) k‖
      ≤ 6 * sWidth p α + 4 :=
  IntMul.HvdH.SPf.Sapprox_bound p s t α k hs ht hα hαp U hU
