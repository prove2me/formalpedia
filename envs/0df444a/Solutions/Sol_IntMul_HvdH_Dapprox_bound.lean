-- Prove2me | solution 1 for IntMul.HvdH.Dapprox_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T23:19:51.846991+00:00
-- url     : https://prove2.me/submissions/2bd5b60b-3cec-40a0-9237-d38a879ff8ca

import Definitions.Def_IntMul_HvdH_DiagApprox
import Theorems.Thm_IntMul_HvdH_expPos_bound

open Complex

namespace IntMul.HvdH.DiagPf
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

lemma round_floor (s t l : ℕ) (hs : 0 < s) :
    ⌊(t * l : ℝ) / s + 1 / 2⌋ = (((2 * t * l + s) / (2 * s) : ℕ) : ℤ) := by
  set q := (2 * t * l + s) / (2 * s)
  have h1 : q * (2 * s) ≤ 2 * t * l + s := Nat.div_mul_le_self _ _
  have h2 : 2 * t * l + s < (q + 1) * (2 * s) :=
    calc 2 * t * l + s < 2 * s * (q + 1) := Nat.lt_mul_div_succ _ (by omega)
      _ = (q + 1) * (2 * s) := by ring
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h1' : (q : ℝ) * (2 * s) ≤ 2 * t * l + s := by exact_mod_cast h1
  have h2' : (2 * t * l + s : ℝ) < (q + 1) * (2 * s) := by exact_mod_cast h2
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [div_add' _ _ _ hsR.ne', le_div_iff₀ hsR]; nlinarith
  · rw [div_add' _ _ _ hsR.ne', div_lt_iff₀ hsR]; nlinarith

theorem Dapprox_bound (p s t α : ℕ) (hs : 0 < s) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ l, ‖toC (U l)‖ ≤ 2 ^ p) (l : ℕ) :
    ‖toC (Dapprox p s t α U l) -
      ((Real.exp (Real.pi * α ^ 2 * ((t * l : ℝ) / s - ⌊(t * l : ℝ) / s + 1 / 2⌋) ^ 2) /
        2 ^ (2 * α ^ 2 - 2) : ℝ) : ℂ) * toC (U l)‖ < 3 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  set q : ℕ := (2 * t * l + s) / (2 * s)
  set β : ℝ := (t * l : ℝ) / s - ⌊(t * l : ℝ) / s + 1 / 2⌋ with hβ
  have hfl := round_floor s t l hs
  -- |β| ≤ 1/2
  have hβ1 : |β| ≤ 1 / 2 := by
    have a := Int.floor_le ((t * l : ℝ) / s + 1 / 2)
    have b := Int.lt_floor_add_one ((t * l : ℝ) / s + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  -- α²β² = α² k / s²
  have hk : (α : ℝ) ^ 2 * β ^ 2 = ((α ^ 2 * kOf s t l : ℕ) : ℝ) / ((s ^ 2 : ℕ) : ℝ) := by
    have hb : β = (((t * l : ℕ) : ℝ) - s * q) / s := by
      rw [hβ, hfl, Int.cast_natCast, Nat.cast_mul]; field_simp; rfl
    have hkO : ((kOf s t l : ℕ) : ℝ) = (((t * l : ℕ) : ℝ) - s * q) ^ 2 := by
      unfold kOf
      rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      rfl
    rw [hb]; push_cast at hkO ⊢; rw [hkO]; field_simp
  set σ : ℕ := 2 * α ^ 2 - 2
  have hσR : (σ : ℝ) = 2 * α ^ 2 - 2 := by
    have : 2 ≤ 2 * α ^ 2 := by nlinarith
    simp only [σ]; push_cast [Nat.cast_sub this]; ring
  have hα2 : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ α := by exact_mod_cast hα
    nlinarith
  have hexp : Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2) ≤ 2 ^ σ := by
    have hβ2 : β ^ 2 ≤ 1 / 4 := by
      have := sq_abs β; nlinarith [abs_nonneg β]
    have hpi := Real.pi_lt_d2
    have hl := Real.log_two_gt_d9
    calc Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2)
        ≤ Real.exp (σ * Real.log 2) := by
          apply Real.exp_le_exp.2
          rw [hσR]
          have a1 : Real.pi * (α : ℝ) ^ 2 * β ^ 2 ≤ Real.pi * (α : ℝ) ^ 2 * (1 / 4) :=
            mul_le_mul_of_nonneg_left hβ2 (by positivity)
          have a2 : Real.pi * (α : ℝ) ^ 2 ≤ 3.15 * (α : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hpi.le (by positivity)
          have a3 : (2 * (α : ℝ) ^ 2 - 2) * 0.6931471803 ≤ (2 * (α : ℝ) ^ 2 - 2) * Real.log 2 :=
            mul_le_mul_of_nonneg_left hl.le (by linarith)
          linarith
      _ = 2 ^ σ := by rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have hσn : σ ≤ 2 * p := by simp only [σ]; omega
  have hjk : Real.pi * ((α ^ 2 * kOf s t l : ℕ) : ℝ) / ((s ^ 2 : ℕ) : ℝ)
      = Real.pi * (α : ℝ) ^ 2 * β ^ 2 := by rw [mul_assoc, hk, mul_div_assoc]
  have hb := expPos_bound p (s ^ 2) (α ^ 2 * kOf s t l) σ (by positivity)
    (by rw [hjk]; exact hexp) hσn
  rw [hjk] at hb
  set dp : ℝ := (2 ^ σ)⁻¹ * Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2) with hdp
  have hdpe : Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2) / 2 ^ (2 * α ^ 2 - 2) = dp := by
    rw [hdp, div_eq_inv_mul]
  rw [hdpe]
  set dt : ℤ := dTilde p s t α l
  have hdt : |(dt : ℝ) - 2 ^ p * dp| ≤ 1 := hb
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hpZ : (0 : ℤ) < 2 ^ p := by positivity
  -- rounding error
  have hround : ‖toC (Dapprox p s t α U l) - (dt : ℂ) * toC (U l) / 2 ^ p‖ ≤ 3 / 2 := by
    have hsC : (((2 ^ p : ℤ) : ℝ) : ℂ) = (2 : ℂ) ^ p := by push_cast; rfl
    refine (norm_le_of_re_im (c := 1) ?_ ?_).trans (by norm_num)
    · rw [← hsC, Complex.sub_re, Complex.div_ofReal_re, toC_re]
      have h := tdiv_err (dt * (U l).1) (2 ^ p) hpZ
      simp only [Dapprox] at h ⊢
      convert h using 2
      simp [toC]
      rfl
    · rw [← hsC, Complex.sub_im, Complex.div_ofReal_im, toC_im]
      have h := tdiv_err (dt * (U l).2) (2 ^ p) hpZ
      simp only [Dapprox] at h ⊢
      convert h using 2
      simp [toC]
      rfl
  have happ : ‖(dt : ℂ) * toC (U l) / 2 ^ p - (dp : ℂ) * toC (U l)‖ ≤ 1 := by
    have e : (dt : ℂ) * toC (U l) / 2 ^ p - (dp : ℂ) * toC (U l)
        = ((((dt : ℝ) - 2 ^ p * dp) / 2 ^ p : ℝ) : ℂ) * toC (U l) := by
      push_cast; field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hp]
    calc |(dt : ℝ) - 2 ^ p * dp| / 2 ^ p * ‖toC (U l)‖ ≤ 1 / 2 ^ p * 2 ^ p :=
          mul_le_mul (div_le_div_of_nonneg_right hdt hp.le) (hU l) (norm_nonneg _) (by positivity)
      _ = 1 := by field_simp
  calc ‖toC (Dapprox p s t α U l) - (dp : ℂ) * toC (U l)‖
      ≤ ‖toC (Dapprox p s t α U l) - (dt : ℂ) * toC (U l) / 2 ^ p‖
        + ‖(dt : ℂ) * toC (U l) / 2 ^ p - (dp : ℂ) * toC (U l)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 / 2 + 1 := add_le_add hround happ
    _ < 3 := by norm_num

end IntMul.HvdH.DiagPf

open IntMul.HvdH in
theorem solution (p s t α : ℕ) (hs : 0 < s) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ l, ‖((U l).1 : ℂ) + ((U l).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) (l : ℕ) :
    ‖(((Dapprox p s t α U l).1 : ℂ) + ((Dapprox p s t α U l).2 : ℂ) * Complex.I) -
      ((Real.exp (Real.pi * α ^ 2 * ((t * l : ℝ) / s - ⌊(t * l : ℝ) / s + 1 / 2⌋) ^ 2) /
        2 ^ (2 * α ^ 2 - 2) : ℝ) : ℂ) * (((U l).1 : ℂ) + ((U l).2 : ℂ) * Complex.I)‖ < 3 :=
  IntMul.HvdH.DiagPf.Dapprox_bound p s t α hs hα hαp U hU l
