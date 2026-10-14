-- Prove2me | solution 1 for IntMul.HvdH.twiddle_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T22:10:08.388881+00:00
-- url     : https://prove2.me/submissions/d27be890-796b-4e34-80ab-0f92681bbf46

import Definitions.Def_IntMul_HvdH_Twiddle
import Theorems.Thm_IntMul_HvdH_piBits_bound
import Theorems.Thm_IntMul_HvdH_expBits_bound

open Complex ComplexConjugate

namespace IntMul.HvdH.TwPf
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

lemma int_div_err (m D : ℤ) (hD : 0 < D) :
    |(((m / D : ℤ) : ℝ)) - (m : ℝ) / D| ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : (m / D) * D ≤ m := Int.ediv_mul_le _ hD.ne'
  have h2 : m < (m / D + 1) * D := Int.lt_ediv_add_one_mul_self m hD
  have h1' : ((m / D : ℤ) : ℝ) * D ≤ m := by exact_mod_cast h1
  have h2' : (m : ℝ) < ((m / D : ℤ) + 1) * D := by exact_mod_cast h2
  have e : ((m / D : ℤ) : ℝ) - (m : ℝ) / D = (((m / D : ℤ) : ℝ) * D - m) / D := by field_simp
  rw [e, abs_div, abs_of_pos hD', div_le_iff₀ hD', abs_le]
  constructor <;> nlinarith

lemma int_round_err (m : ℤ) (s : ℕ) :
    |(((m + 2 ^ s) / 2 ^ (s + 1) : ℤ) : ℝ) - (m : ℝ) / 2 ^ (s + 1)| ≤ 1 / 2 := by
  set q := (m + 2 ^ s) / 2 ^ (s + 1)
  have hd : (0 : ℤ) < 2 ^ (s + 1) := by positivity
  have h1 : q * 2 ^ (s + 1) ≤ m + 2 ^ s := Int.ediv_mul_le _ hd.ne'
  have h2 : m + 2 ^ s < (q + 1) * 2 ^ (s + 1) := by
    have := Int.lt_ediv_add_one_mul_self (m + 2 ^ s) hd; linarith
  have h1' : (q : ℝ) * 2 ^ (s + 1) ≤ m + 2 ^ s := by exact_mod_cast h1
  have h2' : (m : ℝ) + 2 ^ s < (q + 1) * 2 ^ (s + 1) := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have hs : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  have e : (q : ℝ) - m / 2 ^ (s + 1) = ((q : ℝ) * 2 ^ (s + 1) - m) / 2 ^ (s + 1) := by
    field_simp
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  constructor <;> nlinarith

lemma toC_mulI (p : ℤ × ℤ) : toC (mulI p) = I * toC p := by
  apply Complex.ext <;> simp [mulI]

lemma toC_mulI_iter (m : ℕ) (p : ℤ × ℤ) : toC (mulI^[m] p) = I ^ m * toC p := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', toC_mulI, ih, pow_succ]; ring

lemma toC_conjZ (p : ℤ × ℤ) : toC (conjZ p) = conj (toC p) := by
  apply Complex.ext <;> simp [conjZ]

lemma norm_exp_sub_le (a b : ℝ) : ‖exp (a * I) - exp (b * I)‖ ≤ |a - b| := by
  have e : exp (a * I) - exp (b * I) = (exp (I * ((a - b : ℝ) : ℂ)) - 1) * exp (b * I) := by
    rw [sub_mul, ← Complex.exp_add, one_mul]; congr 2; push_cast; ring
  rw [e, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem octExp_bound (n k a : ℕ) (hk : 1 ≤ k) (ha : a ≤ k) :
    ‖toC (octExp n k a) - 2 ^ n * exp ((Real.pi * a / (4 * k) : ℝ) * I)‖ ≤ 1 := by
  set M := n + 4
  set θ : ℝ := Real.pi * a / (4 * k)
  set P : ℤ := piBits M
  have hP : |(P : ℝ) - 2 ^ M * Real.pi| ≤ 1 := piBits_bound M
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha' : (a : ℝ) ≤ k := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hD : (0 : ℤ) < 4 * (k : ℤ) := by positivity
  set φ : ℤ := P * a / (4 * k)
  have hφ1 : |(φ : ℝ) - (P * a : ℤ) / ((4 * k : ℤ) : ℝ)| ≤ 1 := int_div_err _ _ hD
  have hφ2 : |((P * a : ℤ) : ℝ) / ((4 * k : ℤ) : ℝ) - 2 ^ M * θ| ≤ 1 / 4 := by
    have e : ((P * a : ℤ) : ℝ) / ((4 * k : ℤ) : ℝ) - 2 ^ M * θ
        = ((P : ℝ) - 2 ^ M * Real.pi) * (a / (4 * k)) := by
      simp only [θ]; push_cast; field_simp
    rw [e, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ a / (4 * k) by positivity)]
    have : (a : ℝ) / (4 * k) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith [abs_nonneg ((P : ℝ) - 2 ^ M * Real.pi)]
  have hφ : |(φ : ℝ) - 2 ^ M * θ| ≤ 5 / 4 := by
    have := abs_sub_le (φ : ℝ) ((P * a : ℤ) / ((4 * k : ℤ) : ℝ)) (2 ^ M * θ); linarith
  have hM : (16 : ℝ) ≤ 2 ^ M := by
    have : (2 : ℝ) ^ M = 16 * 2 ^ n := by simp only [M]; ring
    rw [this]; have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num); linarith
  have hθ : θ ≤ Real.pi / 4 := by
    simp only [θ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hθ0 : 0 ≤ θ := by positivity
  have hin : ‖toC (0, φ)‖ ≤ 2 ^ M := by
    have : toC (0, φ) = ((φ : ℝ) : ℂ) * I := by simp [toC]
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hpi := Real.pi_lt_d2
    rw [abs_le] at hφ ⊢; constructor <;> nlinarith
  have hu := expBits_bound M 0 φ hin
  set u := expBits M 0 φ
  have hz : toC (0, φ) / 2 ^ M = ((φ / 2 ^ M : ℝ) : ℂ) * I := by
    simp [toC]; ring
  rw [show ((0 : ℤ) : ℂ) + (φ : ℂ) * I = toC (0, φ) by simp [toC], hz] at hu
  have hu' : ‖toC u - 2 ^ M * exp (θ * I)‖ ≤ 9 / 4 := by
    have h2 : ‖(2 : ℂ) ^ M * exp (((φ / 2 ^ M : ℝ) : ℂ) * I) - 2 ^ M * exp (θ * I)‖ ≤ 5 / 4 := by
      rw [← mul_sub, norm_mul, norm_pow, Complex.norm_two]
      have := norm_exp_sub_le (φ / 2 ^ M) θ
      have hp : (0 : ℝ) < 2 ^ M := by positivity
      have e : |(φ : ℝ) / 2 ^ M - θ| = |(φ : ℝ) - 2 ^ M * θ| / 2 ^ M := by
        rw [← abs_of_pos hp, ← abs_div, abs_of_pos hp]; congr 1; field_simp
      rw [e] at this
      calc (2 : ℝ) ^ M * ‖exp (((φ / 2 ^ M : ℝ) : ℂ) * I) - exp (θ * I)‖
          ≤ 2 ^ M * (|(φ : ℝ) - 2 ^ M * θ| / 2 ^ M) := mul_le_mul_of_nonneg_left this hp.le
        _ = |(φ : ℝ) - 2 ^ M * θ| := by field_simp
        _ ≤ 5 / 4 := hφ
    have := norm_sub_le_norm_sub_add_norm_sub (toC u)
      ((2 : ℂ) ^ M * exp (((φ / 2 ^ M : ℝ) : ℂ) * I)) (2 ^ M * exp (θ * I))
    have hu2 : ‖toC u - 2 ^ M * exp (((φ / 2 ^ M : ℝ) : ℂ) * I)‖ ≤ 1 := hu
    linarith
  have hoct : octExp n k a = ((u.1 + 2 ^ 3) / 2 ^ (3 + 1), (u.2 + 2 ^ 3) / 2 ^ (3 + 1)) := rfl
  rw [hoct]
  have hsC : (((2 ^ (3 + 1) : ℕ) : ℂ)) = (2 : ℂ) ^ (3 + 1) := by push_cast; norm_num
  have hr : ‖toC ((u.1 + 2 ^ 3) / 2 ^ (3 + 1), (u.2 + 2 ^ 3) / 2 ^ (3 + 1)) - toC u / 2 ^ (3 + 1)‖
      ≤ 3 / 4 := by
    have := norm_le_of_re_im (c := 1 / 2)
      (z := toC ((u.1 + 2 ^ 3) / 2 ^ (3 + 1), (u.2 + 2 ^ 3) / 2 ^ (3 + 1)) - toC u / 2 ^ (3 + 1))
      ?_ ?_
    · linarith
    · rw [← hsC, Complex.sub_re, Complex.div_natCast_re, toC_re, toC_re]
      have h := int_round_err u.1 3; norm_num at h ⊢; exact h
    · rw [← hsC, Complex.sub_im, Complex.div_natCast_im, toC_im, toC_im]
      have h := int_round_err u.2 3; norm_num at h ⊢; exact h
  have ht : ‖toC u / 2 ^ (3 + 1) - 2 ^ n * exp (θ * I)‖ ≤ 9 / 64 := by
    have hM' : (2 : ℂ) ^ M = 2 ^ (3 + 1) * 2 ^ n := by rw [← pow_add]; congr 1; omega
    have eq : toC u / 2 ^ (3 + 1) - 2 ^ n * exp (θ * I)
        = (toC u - 2 ^ M * exp (θ * I)) / 2 ^ (3 + 1) := by rw [hM']; field_simp
    rw [eq, norm_div, norm_pow, Complex.norm_two]
    norm_num; linarith
  have := norm_sub_le_norm_sub_add_norm_sub
    (toC ((u.1 + 2 ^ 3) / 2 ^ (3 + 1), (u.2 + 2 ^ 3) / 2 ^ (3 + 1))) (toC u / 2 ^ (3 + 1))
    (2 ^ n * exp (θ * I))
  linarith

lemma I_pow_eq (m : ℕ) : I ^ m = exp (m * (Real.pi / 2 * I)) := by
  rw [Complex.exp_nat_mul, exp_pi_div_two_mul_I]

theorem twiddle_bound (n k j : ℕ) (hk : 0 < k) :
    ‖toC (twiddle n k j) - 2 ^ n * exp (2 * Real.pi * I * j / k)‖ ≤ 1 := by
  set j' := j % k with hj'def
  set q := 8 * j' / k with hqdef
  set r := 8 * j' % k with hrdef
  set N := j / k
  have hj : j = k * N + j' := (Nat.div_add_mod j k).symm
  have h8 : 8 * j' = k * q + r := (Nat.div_add_mod (8 * j') k).symm
  have hr : r < k := Nat.mod_lt _ hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hjc : (j : ℂ) = k * N + j' := by exact_mod_cast hj
  have h8c : 8 * (j' : ℂ) = k * q + r := by exact_mod_cast h8
  have htw : twiddle n k j = if q % 2 = 0 then mulI^[q / 2] (octExp n k r)
      else mulI^[q / 2 + 1] (conjZ (octExp n k (k - r))) := rfl
  rw [htw]
  split_ifs with hq
  · set m := q / 2
    have hqm : q = 2 * m := by omega
    have hqc : (q : ℂ) = 2 * m := by exact_mod_cast hqm
    have hE : exp (2 * Real.pi * I * j / k) =
        I ^ m * exp ((Real.pi * r / (4 * k) : ℝ) * I) := by
      rw [I_pow_eq, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨N, ?_⟩
      have hjc' : (j : ℂ) = k * N + (k * (2 * m) + r) / 8 := by
        rw [hjc]; linear_combination (1 / 8 : ℂ) * h8c + (k / 8 : ℂ) * hqc
      rw [hjc']; push_cast; field_simp; ring
    rw [hE, toC_mulI_iter, mul_left_comm, ← mul_sub, norm_mul, norm_pow, Complex.norm_I, one_pow,
      one_mul]
    exact octExp_bound n k r hk hr.le
  · set m := q / 2
    have hqm : q = 2 * m + 1 := by omega
    have hqc : (q : ℂ) = 2 * m + 1 := by exact_mod_cast hqm
    have hE : exp (2 * Real.pi * I * j / k) =
        I ^ (m + 1) * conj (exp ((Real.pi * (k - r : ℕ) / (4 * k) : ℝ) * I)) := by
      rw [← Complex.exp_conj, I_pow_eq, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨N, ?_⟩
      have hjc' : (j : ℂ) = k * N + (k * (2 * m + 1) + r) / 8 := by
        rw [hjc]; linear_combination (1 / 8 : ℂ) * h8c + (k / 8 : ℂ) * hqc
      rw [hjc', map_mul, Complex.conj_ofReal, Complex.conj_I, Nat.cast_sub hr.le]
      push_cast; field_simp; ring
    rw [hE, toC_mulI_iter, toC_conjZ, mul_left_comm, ← mul_sub, norm_mul, norm_pow,
      Complex.norm_I, one_pow, one_mul]
    have : conj (toC (octExp n k (k - r))) - 2 ^ n * conj (exp ((Real.pi * (k - r : ℕ) / (4 * k) : ℝ) * I))
        = conj (toC (octExp n k (k - r)) - 2 ^ n * exp ((Real.pi * (k - r : ℕ) / (4 * k) : ℝ) * I)) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [this, Complex.norm_conj]
    exact octExp_bound n k (k - r) hk (Nat.sub_le _ _)

end IntMul.HvdH.TwPf

open IntMul.HvdH in
theorem solution (n k j : ℕ) (hk : 0 < k) :
    ‖((twiddle n k j).1 : ℂ) + ((twiddle n k j).2 : ℂ) * Complex.I -
      2 ^ n * Complex.exp (2 * Real.pi * Complex.I * j / k)‖ ≤ 1 :=
  IntMul.HvdH.TwPf.twiddle_bound n k j hk
