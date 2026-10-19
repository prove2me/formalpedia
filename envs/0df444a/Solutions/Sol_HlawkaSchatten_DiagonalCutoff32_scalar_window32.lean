-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff32.scalar_window32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:12.626278+00:00
-- url     : https://prove2.me/submissions/87d29e3e-f7f2-4ee3-88d1-344f87b4101d

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false

/-
Scalar estimates on the window 32 ≤ p ≤ 50.

Adapted from the scalar section for the window [50,62], which builds on
Ezzeri Esa's Apache-2.0 formalization of the diagonal construction.

The witness is t = (3/(4p))^{1/p}. Writing x = 1/p, the cyclic numerator and
denominator at the witness are bounded by explicit polynomials in x
(`Nlo`, `Dup`), the envelope deficit by `Glo`, and the two resulting
polynomial certificates are checked on x ∈ [1/50, 1/32] by expansion around
x = 1/32 (the tight end), using the hints `s^k ≤ h^(k-1) s` on `s ∈ [0, h]`.
The bound `log p ≤ log(135/4) + 4p/135 - 1` (tangent at p = 135/4) is used
uniformly over the whole window. The upper bound `p/2` uses a quadratic lower
bound for `2^{1/p}`. The file is self-contained.

The second part proves sharpened envelope bounds `scalarEnvelope p q < cyclicConstant p`
on eight sub-slabs of [32, 50] (`envelope_1` … `envelope_8`). On [40, 42] the value
q = 0.3768 is not admissible (at p = 40 the envelope exceeds the cyclic constant), so
that slab is proved with q = 37682/100000 (`envelope_6_q37682`).
-/

namespace HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten.DiagonalConstruction

/-! ### Elementary analytic bounds -/

lemma exp_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1+x+x^2/2+x^3/6+x^4/12 := by
  have h := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [pow_nonneg hx 4]

lemma exp_neg_quartic_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1-x+x^2/2-x^3/6-x^4/12 ≤ Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

lemma one_sub_exp_neg_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x-x^2/2+x^3/6-x^4/12 ≤ 1-Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

lemma log_one_add_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.log (1+u) ≤ u-u^2/2+2*u^3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; linarith) 2
  have hh := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu] at hh
  have hd : 0 < 1-u := by linarith
  have he : u^3/(1-u) ≤ 2*u^3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (pow_nonneg hu 3) (show 0 ≤ 1-2*u by linarith)]
  linarith

lemma log_two_add_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (2+x) ≤ 6931471808/10^10+x/2-x^2/8+x^3/4 := by
  have h := log_one_add_upper (u := x/2) (by positivity) (by linarith)
  have he : Real.log (2+x) = Real.log 2+Real.log (1+x/2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  rw [he]
  nlinarith [Real.log_two_lt_d9]

lemma log_two_add {x : ℝ} (hx : 0 ≤ x) :
    6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4 ≤ Real.log (2 + x) := by
  have hsplit : Real.log (2 + x) = Real.log 2 + Real.log ((2 + x) / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have hlo := Real.one_sub_inv_le_log_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hinv : 1 - ((2 + x) / 2)⁻¹ = x / (2 + x) := by field_simp; ring
  have hfrac : x / 2 - x ^ 2 / 4 ≤ x / (2 + x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hx 3]
  rw [hsplit]; linarith [Real.log_two_gt_d9]

lemma log_three_quarters_neg : Real.log (3 / 4 : ℝ) < 0 :=
  Real.log_neg (by norm_num) (by norm_num)

/-! ### Basic facts about the cyclic quantities -/

lemma cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity

lemma cyclicA_nonneg (p : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cyclicA p t := by
  unfold cyclicA
  have := Real.rpow_nonneg ht p
  positivity

lemma cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]

lemma cyclicA_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    cyclicA p t ^ p = t ^ p + 2 := by
  rw [cyclicA, ← Real.rpow_mul (by positivity : 0 ≤ t ^ p + 2),
    one_div_mul_cancel hp.ne', Real.rpow_one]

lemma cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (cyclicB_nonneg p t) hp).mp
  rw [cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith

/-- Positivity of the cyclic denominator (proved here for `1 < p`, `0 ≤ t`). -/
lemma denominator_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by
  have hp0 : 0 < p := by linarith
  have habs : |1 - t| ^ p ≤ 1 + t ^ p := by
    rcases le_total t 1 with h | h
    · have h1 : |1 - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
      rw [Real.one_rpow] at this
      linarith [Real.rpow_nonneg ht p]
    · have h1 : |1 - t| ≤ t := abs_le.mpr ⟨by linarith, by linarith⟩
      have := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
      linarith
  have htwo : (2 : ℝ) < 2 ^ p := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
    simpa using this
  have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht p
  have hlt : cyclicB p t ^ p < (2 * cyclicA p t) ^ p := by
    rw [Real.mul_rpow (by norm_num) (cyclicA_nonneg p ht), cyclicA_rpow hp0 ht, cyclicB_rpow hp0]
    nlinarith
  have hBA : cyclicB p t < 2 * cyclicA p t :=
    (Real.rpow_lt_rpow_iff (cyclicB_nonneg p t)
      (by have := cyclicA_nonneg p ht; positivity) hp0).mp hlt
  linarith

/-! ### The witness `(3/(4p))^{1/p}` -/

/-- The cyclic witness `(3/(4p))^{1/p}`. -/
noncomputable def witness (p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))

lemma witness_power {p : ℝ} (hp : 0 < p) :
    witness p ^ p = 3 / 4 * p⁻¹ := by
  rw [witness, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -((Real.log p - Real.log (3 / 4)) * p⁻¹) * p = Real.log (3 / 4) - Real.log p := by
    field_simp
    ring
  rw [he, Real.exp_sub, Real.exp_log hp, Real.exp_log (by norm_num)]
  field_simp

lemma inverse_bounds {p : ℝ} (hp : 32 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/32 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩

lemma inverse_lower {p : ℝ} (hp : 32 ≤ p) (hhi : p ≤ 50) : 1/50 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi

/-- Tangent bound for `log p` at `p = 135/4`, scaled by `1/p`. -/
lemma witness_scaled_tangent {p : ℝ} (hp : 0 < p) :
    (Real.log p - Real.log (3/4)) * p⁻¹ ≤ (2806662491/10^9 : ℝ) * p⁻¹ + 4/135 := by
  have h1 : Real.log (p / (3/4)) = Real.log p - Real.log (3/4) :=
    Real.log_div hp.ne' (by norm_num)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < p / (3/4) / 45 by positivity)
  have h3 : Real.log (p / (3/4) / 45) = Real.log (p / (3/4)) - Real.log 45 :=
    Real.log_div (by positivity) (by norm_num)
  have h4 : Real.log (45 : ℝ) = 2 * Real.log 3 + Real.log 5 := by
    rw [show (45 : ℝ) = 3 ^ 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have h5 : p / (3/4) / 45 = 4/135 * p := by ring
  have hb : Real.log p - Real.log (3/4) ≤ 2806662491/10^9 + 4/135 * p := by
    rw [h3, h1, h4, h5] at h2
    linarith [Real.log_three_lt_d9, Real.log_five_lt_d9]
  have hm := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hp.le)
  have he : (2806662491/10^9 + 4/135 * p) * p⁻¹ = (2806662491/10^9 : ℝ) * p⁻¹ + 4/135 := by
    field_simp
  linarith

lemma scaled {p : ℝ} (hp : 32 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (2806662491/10^9 : ℝ)*p⁻¹+4/135 ∧
    (2806662491/10^9 : ℝ)*p⁻¹+4/135 < 1/5 := by
  have hi := inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), log_three_quarters_neg]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩

lemma witness_bounds {p : ℝ} (hp : 32 ≤ p) :
    1/2 ≤ witness p ∧ witness p ≤ 1 := by
  have hl := scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩

lemma cyclicA_exp {p : ℝ} (hp : 32 ≤ p) :
    cyclicA p (witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

/-! ### Polynomial bounds in `x = 1/p` -/

/-- Lower bound for the cyclic numerator at the witness. -/
noncomputable def Nlo (x : ℝ) : ℝ :=
  let z := (2806662491/10^9 : ℝ)*x+4/135
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)

/-- Upper bound for the cyclic denominator at the witness. -/
noncomputable def Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)

/-- Lower bound for the envelope deficit. -/
noncomputable def Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

set_option maxHeartbeats 4000000 in
/-- Polynomial certificate for the linear lower bound, on `x ∈ [1/50, 1/32]`. -/
theorem linear_certificate {x : ℝ} (hlo : 1/50 ≤ x) (hhi : x ≤ 1/32) :
    (448/1000 : ℝ) * Dup x < x * Nlo x := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/32 - s := ⟨1/32 - x, by linarith, by ring⟩
  have hh : s ≤ 9/800 := by linarith
  have p2 : s ^ 2 ≤ (9/800 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (9/800 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (9/800 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (9/800 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (9/800 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (9/800 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (9/800 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (9/800 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (9/800 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (9/800 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (9/800 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (9/800 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (9/800 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (9/800 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (9/800 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have q2 := pow_nonneg hs 2
  have q3 := pow_nonneg hs 3
  have q4 := pow_nonneg hs 4
  have q5 := pow_nonneg hs 5
  have q6 := pow_nonneg hs 6
  have q7 := pow_nonneg hs 7
  have q8 := pow_nonneg hs 8
  have q9 := pow_nonneg hs 9
  have q10 := pow_nonneg hs 10
  have q11 := pow_nonneg hs 11
  have q12 := pow_nonneg hs 12
  have q13 := pow_nonneg hs 13
  have q14 := pow_nonneg hs 14
  have q15 := pow_nonneg hs 15
  have q16 := pow_nonneg hs 16
  dsimp only [Dup, Nlo]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16
  linarith

set_option maxHeartbeats 4000000 in
/-- Polynomial certificate for the envelope comparison, on `x ∈ [1/50, 1/32]`. -/
theorem envelope_certificate {x : ℝ} (hlo : 1/50 ≤ x) (hhi : x ≤ 1/32) :
    (1 - 386/1000 : ℝ) * Dup x < Nlo x * (2 * Glo x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/32 - s := ⟨1/32 - x, by linarith, by ring⟩
  have hh : s ≤ 9/800 := by linarith
  have p2 : s ^ 2 ≤ (9/800 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (9/800 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (9/800 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (9/800 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (9/800 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (9/800 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (9/800 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (9/800 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (9/800 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (9/800 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (9/800 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (9/800 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (9/800 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (9/800 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (9/800 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (9/800 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have q2 := pow_nonneg hs 2
  have q3 := pow_nonneg hs 3
  have q4 := pow_nonneg hs 4
  have q5 := pow_nonneg hs 5
  have q6 := pow_nonneg hs 6
  have q7 := pow_nonneg hs 7
  have q8 := pow_nonneg hs 8
  have q9 := pow_nonneg hs 9
  have q10 := pow_nonneg hs 10
  have q11 := pow_nonneg hs 11
  have q12 := pow_nonneg hs 12
  have q13 := pow_nonneg hs 13
  have q14 := pow_nonneg hs 14
  have q15 := pow_nonneg hs 15
  have q16 := pow_nonneg hs 16
  have q17 := pow_nonneg hs 17
  dsimp only [Dup, Nlo, Glo]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17
  linarith

/-! ### Bounds at the witness -/

set_option maxHeartbeats 4000000 in
lemma numerator_lower {p : ℝ} (hp : 32 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (witness p)-(3 : ℝ)^(1/p)*|2-witness p| := by
  set x := p⁻¹ with hxdef
  have hi := inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := witness_bounds hp
  have hl := scaled hp
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := 2806662491/10^9*x+4/135
  have hc0 : 0 ≤ C := by dsimp [C]; positivity
  have hc1 : C ≤ 1 := by dsimp [C]; linarith [hi.2]
  have hz0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hz1 : Z ≤ 1 := by dsimp [Z]; linarith [hl.2.2]
  have hroot : (3 : ℝ)^(1/p) = Real.exp (Real.log 3*x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hc : Real.log 3*x ≤ C := by
    apply mul_le_mul_of_nonneg_right _ hx0
    linarith [Real.log_three_lt_d9]
  have hr := (Real.exp_le_exp.mpr hc).trans (exp_quartic hc0 hc1)
  have hw : Real.exp (-Z) ≤ witness p := by
    apply Real.exp_le_exp.mpr
    dsimp [Z]
    linarith [hl.2.1]
  have htup : 2-witness p ≤ 1+Z-Z^2/2+Z^3/6+Z^4/12 := by
    have h := exp_neg_quartic_lower hz0 hz1
    linarith
  have habs : |2-witness p| = 2-witness p := abs_of_nonneg (by linarith [ht.2])
  have hprod := mul_le_mul hr htup (show 0 ≤ 2-witness p by linarith [ht.2])
    (show 0 ≤ 1+C+C^2/2+C^3/6+C^4/12 by positivity)
  have ha := log_two_add (show 0 ≤ 3/4*x by positivity)
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2+3/4*x)) hx0)
  rw [← cyclicA_exp hp] at hA
  have hy0 : 0 ≤ (6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x := by
    apply mul_nonneg _ hx0
    nlinarith [hi.2]
  have hyy := mul_le_mul_of_nonneg_right ha hx0
  have hAmono : 1+(6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x+
      ((6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x)^2/2 ≤
      1+Real.log (2+3/4*x)*x+(Real.log (2+3/4*x)*x)^2/2 := by
    have h2 := pow_le_pow_left₀ hy0 hyy 2
    linarith
  rw [hroot,habs]
  dsimp [Nlo,C,Z] at hprod ⊢
  nlinarith

set_option maxHeartbeats 4000000 in
lemma denominator_upper {p : ℝ} (hp : 32 ≤ p) :
    6*cyclicA p (witness p)-3*cyclicB p (witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hk0 : 0 ≤ 3/4*x := by positivity
  have hk1 : 3/4*x ≤ 1 := by linarith [hi.2]
  have ha := log_two_add_upper hk0 hk1
  have hy0 : 0 ≤ Real.log (2+3/4*x)*x :=
    mul_nonneg (Real.log_nonneg (by linarith)) hx0
  let T : ℝ := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  have hyy : Real.log (2+3/4*x)*x ≤ T := by
    have h := mul_le_mul_of_nonneg_right ha hx0
    dsimp [T]
    nlinarith
  have ht0 : 0 ≤ T := hy0.trans hyy
  have hx2 := pow_le_pow_left₀ hx0 hi.2 2
  have hx3 := pow_le_pow_left₀ hx0 hi.2 3
  have ht1 : T ≤ 1 := by
    dsimp [T]
    have hinner : 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 ≤ 1 := by
      nlinarith [sq_nonneg x]
    have h := mul_le_mul_of_nonneg_right hinner hx0
    nlinarith [hi.2]
  have hE := (Real.exp_le_exp.mpr hyy).trans (exp_quartic ht0 ht1)
  rw [← cyclicA_exp hp] at hE
  have hB := cyclicB_ge_two (t := witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

lemma Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/32) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma Nlo_pos {x : ℝ} (hlo : 1/50 ≤ x) (hhi : x ≤ 1/32) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := linear_certificate hlo hhi
  have hd := Dup_pos hx hhi
  nlinarith

lemma Glo_pos {x : ℝ} (hlo : 1/50 ≤ x) (hhi : x ≤ 1/32) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

/-! ### Upper bound `cyclicRatio ≤ p/2` -/

lemma cyclicA_lower {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    1 + (693 / 1000 : ℝ) * (1 / p) + (693 / 1000 : ℝ) ^ 2 / 2 * (1 / p) ^ 2 ≤
      cyclicA p t := by
  have hx0 : 0 ≤ 1 / p := one_div_nonneg.mpr hp.le
  have hlog : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hlog hx0
  have hy0 : 0 ≤ (693 / 1000 : ℝ) * (1 / p) := by positivity
  have he := Real.quadratic_le_exp_of_nonneg (mul_nonneg (Real.log_nonneg
    (by norm_num : (1 : ℝ) ≤ 2)) hx0)
  have hsq := pow_le_pow_left₀ hy0 hm 2
  have hr : 1 + (693 / 1000 : ℝ) * (1 / p) + (693 / 1000 : ℝ) ^ 2 / 2 * (1 / p) ^ 2 ≤
      (2 : ℝ) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have : ((693 / 1000 : ℝ) * (1 / p)) ^ 2 = (693 / 1000 : ℝ) ^ 2 * (1 / p) ^ 2 := by ring
    linarith
  exact hr.trans (Real.rpow_le_rpow (by norm_num)
    (by linarith [Real.rpow_nonneg ht p]) hx0)

lemma cyclicB_upper {p t : ℝ} (hp : 32 ≤ p) (ht : t ∈ Set.Icc (1 / 2) 2) :
    cyclicB p t ≤ 2 + (1 / p) / 1000000 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have habs : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpow : (2 : ℝ) ^ p ≥ 4194304 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (22 : ℝ) ≤ p by linarith)
    norm_num at h
    linarith
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have htail : 4 / (2 : ℝ) ^ p ≤ 1 / 1000000 := by
    rw [div_le_iff₀ htwo]
    linarith
  have hb : cyclicB p t ≤ (2 + (2 : ℝ) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow (by positivity) _ hx0
    have h := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    simp only [Real.one_rpow] at h
    linarith
  have heq : (2 + (2 : ℝ) ^ p) ^ (1 / p) =
      2 * (1 + 2 / (2 : ℝ) ^ p) ^ (1 / p) := by
    rw [show 2 + (2 : ℝ) ^ p = (2 : ℝ) ^ p * (1 + 2 / (2 : ℝ) ^ p) by
      field_simp; ring,
      Real.mul_rpow htwo.le (by positivity), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hconc := rpow_one_add_le_one_add_mul_self
    (s := 2 / (2 : ℝ) ^ p)
    (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) htwo.le]) hx0 hx1
  rw [heq] at hb
  have hm := mul_le_mul_of_nonneg_left hconc (by norm_num : (0 : ℝ) ≤ 2)
  have ht0 := mul_le_mul_of_nonneg_right htail hx0
  have halg : 2 * (1 + (1/p) * (2 / (2 : ℝ) ^ p)) =
      2 + (4 / (2 : ℝ) ^ p) * (1/p) := by ring
  rw [halg] at hm
  nlinarith

lemma cyclicRatio_le_half_exponent {p t : ℝ} (hp : 32 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2) 2) : cyclicRatio p t ≤ p / 2 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hden := denominator_pos (show 1 < p by linarith) ht0
  have hA := cyclicA_lower (t := t) hp0 ht0
  have hB := cyclicB_upper hp ht
  have hthree : 1 ≤ (3 : ℝ) ^ (1/p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnum : 3 * cyclicA p t - (3 : ℝ) ^ (1/p) * |2-t| ≤ 4 * cyclicA p t - 2 := by
    have htA : t ≤ cyclicA p t := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 p)
        (show t ^ p ≤ t ^ p + 2 by linarith) (one_div_nonneg.mpr hp0.le)
      rw [← Real.rpow_mul ht0, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
      exact h
    have h := mul_le_mul_of_nonneg_right hthree (abs_nonneg (2-t))
    rw [abs_of_nonneg (by linarith [ht.2])] at h
    rw [abs_of_nonneg (by linarith [ht.2])]
    nlinarith
  set x := 1 / p with hxdef
  have hpx : p * x = 1 := mul_one_div_cancel hp0.ne'
  have hx0 : 0 ≤ x := by positivity
  have hx : x ≤ 1 / 32 := one_div_le_one_div_of_le (by norm_num) hp
  have hkey : 2 + 1/1000 ≤ (3*p-4) * ((693 / 1000 : ℝ) * x + (693 / 1000 : ℝ) ^ 2 / 2 * x ^ 2) := by
    have hid : (3*p-4) * ((693 / 1000 : ℝ) * x + (693 / 1000 : ℝ) ^ 2 / 2 * x ^ 2) =
        3 * (693 / 1000) + (3 * (693 / 1000 : ℝ) ^ 2 / 2 - 4 * (693 / 1000)) * x -
          2 * (693 / 1000 : ℝ) ^ 2 * x ^ 2 := by
      linear_combination (3 * (693 / 1000 : ℝ) + 3 * (693 / 1000 : ℝ) ^ 2 / 2 * x) * hpx
    rw [hid]
    nlinarith
  have hAl := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3*p-4 by linarith)
  have hBu := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*p/2 by positivity)
  have hfinal : 4 * cyclicA p t - 2 ≤ (p/2) * (6 * cyclicA p t - 3 * cyclicB p t) := by
    have hpx' : (3*p/2) * (2 + x / 1000000) = 3*p + 3/2000000 := by
      linear_combination (3/2000000 : ℝ) * hpx
    nlinarith
  exact (div_le_iff₀ hden).mpr (hnum.trans hfinal)

lemma cyclicRatio_bddAbove {p : ℝ} (hp : 32 ≤ p) :
    BddAbove (cyclicRatio p '' Set.Icc (1 / 2 : ℝ) 2) := by
  refine ⟨p / 2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact cyclicRatio_le_half_exponent hp ht

lemma cyclicRatio_le_constant {p t : ℝ} (hp : 32 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p :=
  le_csSup (cyclicRatio_bddAbove hp) (Set.mem_image_of_mem (cyclicRatio p) ht)

lemma cyclicConstant_le_half_exponent {p : ℝ} (hp : 32 ≤ p) :
    cyclicConstant p ≤ p / 2 := by
  apply csSup_le
  · exact ⟨cyclicRatio p 1, Set.mem_image_of_mem _ ⟨by norm_num, by norm_num⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact cyclicRatio_le_half_exponent hp ht

/-! ### The two lower bounds -/

lemma cyclicConstant_gt_linear {p : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50) :
    (448 / 1000 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := inverse_bounds hp
  have hi' := inverse_lower hp hp'
  have ht := witness_bounds hp
  have hD := denominator_pos (show 1 < p by linarith)
    (show 0 ≤ witness p by linarith [ht.1])
  have hn := numerator_lower hp
  have hd := denominator_upper hp
  have hc := linear_certificate hi' hi.2
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (448 / 1000 : ℝ) * p < cyclicRatio p (witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 448 / 1000 * p by positivity)
    have : p * (p⁻¹ * Nlo p⁻¹) = Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (cyclicRatio_le_constant hp ⟨ht.1, by linarith [ht.2]⟩)

lemma power_tail {p : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50) :
    (386/1000 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (386/1000 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp

lemma envelope_deficit {p : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (386/1000) := by
  have hi := inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (386/1000 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := power_tail hp hp'
  let d := Real.log 2-Real.log (1+a)
  have hdLower : Real.log 2-x^2/1000 < d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have h := Real.log_nonneg (show 1 ≤ 1+a by linarith)
    dsimp [d]
    linarith
  have hL : (6931471803/10^10 : ℝ) < Real.log 2 ∧ Real.log 2 <6931471808/10^10 := by
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have hx2 : x^2/1000 ≤ 1/1000 := by nlinarith [hi.1,hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d*x := mul_nonneg hd0 hi.1.le
  have hdx1 : d*x ≤ 1 := by nlinarith [hL.2,hi.2]
  have he := one_sub_exp_neg_quartic hdx0 hdx1
  have hdx : d*x ≤ 6931471808/10^10*x :=
    mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hfour := pow_le_pow_left₀ hdx0 hdx 4
  have hgl : (6931471803/10^10-x^2/1000)*x < d*x :=
    mul_lt_mul_of_pos_right (by linarith) hi.1
  have hg0 : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hi.1.le
    linarith [hL.1]
  have hcube := pow_le_pow_left₀ hg0 hgl.le 3
  have hroot : scalarEnvelopeRoot p (386/1000) = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp [Glo]
  linarith

lemma envelope_lt {p : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50) :
    scalarEnvelope p (386/1000) < cyclicConstant p := by
  have hi := inverse_bounds hp
  have hi' := inverse_lower hp hp'
  have ht := witness_bounds hp
  have hD := denominator_pos (show 1 < p by linarith)
    (show 0 ≤ witness p by linarith [ht.1])
  have hn := numerator_lower hp
  have hd := denominator_upper hp
  have hg := envelope_deficit hp hp'
  have hc := envelope_certificate hi' hi.2
  have hN0 := Nlo_pos hi' hi.2
  have hG0 := Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (386/1000)) := by linarith
  have hr : scalarEnvelope p (386/1000) < cyclicRatio p (witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (386/1000 : ℝ)) * Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < Nlo p⁻¹ * (2 * Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (386/1000))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (cyclicRatio_le_constant hp ⟨ht.1, by linarith [ht.2]⟩)


/-! ### Sharpened envelope bounds on sub-slabs

On each sub-slab `[a, b]` the witness is `t = (c/p)^{1/p}` with `c = a/n` for a
`{2,3,5}`-smooth integer `n`, so that the tangent bound for `log p` is taken at
`p = a` exactly. The analytic bounds carry one more Taylor term than above. -/

end HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff32.scalar_window32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (386 / 1000) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by
  intro p hp hp'
  exact ⟨HlawkaSchatten.DiagonalCutoff32.cyclicConstant_gt_linear hp hp',
    HlawkaSchatten.DiagonalCutoff32.envelope_lt hp hp',
    HlawkaSchatten.DiagonalCutoff32.cyclicConstant_le_half_exponent hp⟩

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem solution : ∀ p : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (386 / 1000) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by
  exact HlawkaSchatten.DiagonalCutoff32.scalar_window32
