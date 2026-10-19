-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff32.slab_envelopes32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:16.231216+00:00
-- url     : https://prove2.me/submissions/30b5bba1-3494-4196-9480-a3273b3581d8

import Definitions.Def_HlawkaSchatten_DiagonalCutoff32_SlabRadius
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_envelope_certificate_sound
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

lemma log_smooth (i j k : ℕ) :
    Real.log ((2 : ℝ) ^ i * 3 ^ j * 5 ^ k) ≤
      i * (6931471808/10^10) + j * (10986122888/10^10) + k * (16094379126/10^10) := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num at h2 h3 h5
  nlinarith [mul_le_mul_of_nonneg_left h2.le hi, mul_le_mul_of_nonneg_left h3.le hj,
    mul_le_mul_of_nonneg_left h5.le hk]

lemma envelope_ltG {a b n ℓ q p : ℝ} (ha : 32 ≤ a) (hb : b ≤ 50) (hn : 0 < n) (han : a ≤ n)
    (hℓ : Real.log n ≤ ℓ) (hℓ1 : 1 ≤ ℓ) (hℓ5 : (ℓ - 1) * (1/32) + 1/a ≤ 1/5)
    (hq0 : 0 < q) (hq : q ≤ 2/5)
    (hcert : ∀ x : ℝ, 1/b ≤ x → x ≤ 1/a →
      (1 - q) * DupG (a/n) x < NloG (a/n) (ℓ - 1) (1/a) x * (2 * GloG x))
    (hp : a ≤ p) (hp' : p ≤ b) :
    scalarEnvelope p q < cyclicConstant p :=
  envelope_certificate_sound a b n ℓ q p ha hb hn han hℓ hℓ1 hℓ5 hq0 hq hcert hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [32, 33]`, `q = 3851/10000`. -/
theorem envelope_certificate_1 {x : ℝ} (hlo : 1/33 ≤ x) (hhi : x ≤ 1/32) :
    (1 - 3851/10000 : ℝ) * DupG (32/45) x <
      NloG (32/45) (19033312451/5000000000 - 1) (1/32) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/32 - s := ⟨1/32 - x, by linarith, by ring⟩
  have hh : s ≤ 1/1056 := by linarith
  have p2 : s ^ 2 ≤ (1/1056 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/1056 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/1056 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/1056 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/1056 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/1056 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/1056 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/1056 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/1056 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/1056 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/1056 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/1056 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/1056 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/1056 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/1056 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/1056 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/1056 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/1056 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/1056 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_1 : ∀ p : ℝ, 32 ≤ p → p ≤ 33 →
    scalarEnvelope p (3851 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (45 : ℝ) ≤ 19033312451/5000000000 := by
    have h := log_smooth 0 2 1
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 32) (b := 33) (n := 45) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_1 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [33, 34]`, `q = 3839/10000`. -/
theorem envelope_certificate_2 {x : ℝ} (hlo : 1/34 ≤ x) (hhi : x ≤ 1/33) :
    (1 - 3839/10000 : ℝ) * DupG (33/48) x <
      NloG (33/48) (967800253/250000000 - 1) (1/33) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/33 - s := ⟨1/33 - x, by linarith, by ring⟩
  have hh : s ≤ 1/1122 := by linarith
  have p2 : s ^ 2 ≤ (1/1122 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/1122 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/1122 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/1122 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/1122 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/1122 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/1122 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/1122 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/1122 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/1122 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/1122 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/1122 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/1122 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/1122 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/1122 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/1122 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/1122 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/1122 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/1122 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_2 : ∀ p : ℝ, 33 ≤ p → p ≤ 34 →
    scalarEnvelope p (3839 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (48 : ℝ) ≤ 967800253/250000000 := by
    have h := log_smooth 4 1 0
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 33) (b := 34) (n := 48) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_2 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [34, 36]`, `q = 3827/10000`. -/
theorem envelope_certificate_3 {x : ℝ} (hlo : 1/36 ≤ x) (hhi : x ≤ 1/34) :
    (1 - 3827/10000 : ℝ) * DupG (34/48) x <
      NloG (34/48) (967800253/250000000 - 1) (1/34) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/34 - s := ⟨1/34 - x, by linarith, by ring⟩
  have hh : s ≤ 1/612 := by linarith
  have p2 : s ^ 2 ≤ (1/612 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/612 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/612 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/612 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/612 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/612 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/612 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/612 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/612 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/612 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/612 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/612 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/612 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/612 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/612 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/612 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/612 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/612 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/612 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_3 : ∀ p : ℝ, 34 ≤ p → p ≤ 36 →
    scalarEnvelope p (3827 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (48 : ℝ) ≤ 967800253/250000000 := by
    have h := log_smooth 4 1 0
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 34) (b := 36) (n := 48) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_3 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [36, 38]`, `q = 3806/10000`. -/
theorem envelope_certificate_4 {x : ℝ} (hlo : 1/38 ≤ x) (hhi : x ≤ 1/36) :
    (1 - 3806/10000 : ℝ) * DupG (36/50) x <
      NloG (36/50) (1956011503/500000000 - 1) (1/36) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/36 - s := ⟨1/36 - x, by linarith, by ring⟩
  have hh : s ≤ 1/684 := by linarith
  have p2 : s ^ 2 ≤ (1/684 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/684 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/684 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/684 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/684 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/684 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/684 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/684 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/684 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/684 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/684 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/684 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/684 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/684 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/684 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/684 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/684 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/684 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/684 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_4 : ∀ p : ℝ, 36 ≤ p → p ≤ 38 →
    scalarEnvelope p (3806 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (50 : ℝ) ≤ 1956011503/500000000 := by
    have h := log_smooth 1 0 2
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 36) (b := 38) (n := 50) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_4 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [38, 40]`, `q = 3786/10000`. -/
theorem envelope_certificate_5 {x : ℝ} (hlo : 1/40 ≤ x) (hhi : x ≤ 1/38) :
    (1 - 3786/10000 : ℝ) * DupG (38/54) x <
      NloG (38/54) (4986230059/1250000000 - 1) (1/38) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/38 - s := ⟨1/38 - x, by linarith, by ring⟩
  have hh : s ≤ 1/760 := by linarith
  have p2 : s ^ 2 ≤ (1/760 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/760 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/760 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/760 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/760 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/760 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/760 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/760 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/760 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/760 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/760 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/760 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/760 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/760 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/760 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/760 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/760 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/760 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/760 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_5 : ∀ p : ℝ, 38 ≤ p → p ≤ 40 →
    scalarEnvelope p (3786 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (54 : ℝ) ≤ 4986230059/1250000000 := by
    have h := log_smooth 1 3 0
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 38) (b := 40) (n := 54) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_5 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [40, 42]`, `q = 37682/100000`. -/
theorem envelope_certificate_6 {x : ℝ} (hlo : 1/42 ≤ x) (hhi : x ≤ 1/40) :
    (1 - 37682/100000 : ℝ) * DupG (40/60) x <
      NloG (40/60) (4094344563/1000000000 - 1) (1/40) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/40 - s := ⟨1/40 - x, by linarith, by ring⟩
  have hh : s ≤ 1/840 := by linarith
  have p2 : s ^ 2 ≤ (1/840 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/840 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/840 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/840 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/840 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/840 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/840 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/840 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/840 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/840 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/840 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/840 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/840 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/840 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/840 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/840 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/840 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/840 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/840 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

/-- On [40, 42] with q = 0.3768 the bound fails at p = 40; 0.37682 is used instead. -/
theorem envelope_6_q37682 : ∀ p : ℝ, 40 ≤ p → p ≤ 42 →
    scalarEnvelope p (37682 / 100000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (60 : ℝ) ≤ 4094344563/1000000000 := by
    have h := log_smooth 2 1 1
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 40) (b := 42) (n := 60) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_6 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [42, 45]`, `q = 3752/10000`. -/
theorem envelope_certificate_7 {x : ℝ} (hlo : 1/45 ≤ x) (hhi : x ≤ 1/42) :
    (1 - 3752/10000 : ℝ) * DupG (42/60) x <
      NloG (42/60) (4094344563/1000000000 - 1) (1/42) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/42 - s := ⟨1/42 - x, by linarith, by ring⟩
  have hh : s ≤ 1/630 := by linarith
  have p2 : s ^ 2 ≤ (1/630 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/630 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/630 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/630 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/630 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/630 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/630 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/630 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/630 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/630 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/630 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/630 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/630 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/630 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/630 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/630 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/630 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/630 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/630 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_7 : ∀ p : ℝ, 42 ≤ p → p ≤ 45 →
    scalarEnvelope p (3752 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (60 : ℝ) ≤ 4094344563/1000000000 := by
    have h := log_smooth 2 1 1
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 42) (b := 45) (n := 60) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_7 h1 h2) hp hp'

set_option maxHeartbeats 8000000 in
/-- Polynomial certificate for the envelope comparison on `p ∈ [45, 50]`, `q = 3730/10000`. -/
theorem envelope_certificate_8 {x : ℝ} (hlo : 1/50 ≤ x) (hhi : x ≤ 1/45) :
    (1 - 3730/10000 : ℝ) * DupG (45/64) x <
      NloG (45/64) (324912741/78125000 - 1) (1/45) x * (2 * GloG x) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1/45 - s := ⟨1/45 - x, by linarith, by ring⟩
  have hh : s ≤ 1/450 := by linarith
  have p2 : s ^ 2 ≤ (1/450 : ℝ) ^ 1 * s :=
    calc s ^ 2 = s ^ 1 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 1) hs
  have p3 : s ^ 3 ≤ (1/450 : ℝ) ^ 2 * s :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have p4 : s ^ 4 ≤ (1/450 : ℝ) ^ 3 * s :=
    calc s ^ 4 = s ^ 3 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 3) hs
  have p5 : s ^ 5 ≤ (1/450 : ℝ) ^ 4 * s :=
    calc s ^ 5 = s ^ 4 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 4) hs
  have p6 : s ^ 6 ≤ (1/450 : ℝ) ^ 5 * s :=
    calc s ^ 6 = s ^ 5 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 5) hs
  have p7 : s ^ 7 ≤ (1/450 : ℝ) ^ 6 * s :=
    calc s ^ 7 = s ^ 6 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 6) hs
  have p8 : s ^ 8 ≤ (1/450 : ℝ) ^ 7 * s :=
    calc s ^ 8 = s ^ 7 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 7) hs
  have p9 : s ^ 9 ≤ (1/450 : ℝ) ^ 8 * s :=
    calc s ^ 9 = s ^ 8 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 8) hs
  have p10 : s ^ 10 ≤ (1/450 : ℝ) ^ 9 * s :=
    calc s ^ 10 = s ^ 9 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 9) hs
  have p11 : s ^ 11 ≤ (1/450 : ℝ) ^ 10 * s :=
    calc s ^ 11 = s ^ 10 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 10) hs
  have p12 : s ^ 12 ≤ (1/450 : ℝ) ^ 11 * s :=
    calc s ^ 12 = s ^ 11 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 11) hs
  have p13 : s ^ 13 ≤ (1/450 : ℝ) ^ 12 * s :=
    calc s ^ 13 = s ^ 12 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 12) hs
  have p14 : s ^ 14 ≤ (1/450 : ℝ) ^ 13 * s :=
    calc s ^ 14 = s ^ 13 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 13) hs
  have p15 : s ^ 15 ≤ (1/450 : ℝ) ^ 14 * s :=
    calc s ^ 15 = s ^ 14 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 14) hs
  have p16 : s ^ 16 ≤ (1/450 : ℝ) ^ 15 * s :=
    calc s ^ 16 = s ^ 15 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 15) hs
  have p17 : s ^ 17 ≤ (1/450 : ℝ) ^ 16 * s :=
    calc s ^ 17 = s ^ 16 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 16) hs
  have p18 : s ^ 18 ≤ (1/450 : ℝ) ^ 17 * s :=
    calc s ^ 18 = s ^ 17 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 17) hs
  have p19 : s ^ 19 ≤ (1/450 : ℝ) ^ 18 * s :=
    calc s ^ 19 = s ^ 18 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 18) hs
  have p20 : s ^ 20 ≤ (1/450 : ℝ) ^ 19 * s :=
    calc s ^ 20 = s ^ 19 * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 19) hs
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
  have q18 := pow_nonneg hs 18
  have q19 := pow_nonneg hs 19
  have q20 := pow_nonneg hs 20
  dsimp only [DupG, NloG, GloG]
  ring_nf
  ring_nf at p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
  linarith

theorem envelope_8 : ∀ p : ℝ, 45 ≤ p → p ≤ 50 →
    scalarEnvelope p (3730 / 10000) < cyclicConstant p := by
  intro p hp hp'
  have hℓ : Real.log (64 : ℝ) ≤ 324912741/78125000 := by
    have h := log_smooth 6 0 0
    norm_num at h ⊢
    linarith
  exact envelope_ltG (a := 45) (b := 50) (n := 64) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x h1 h2 => envelope_certificate_8 h1 h2) hp hp'


theorem slab_envelopes32_local : ∀ p : ℝ, 32 ≤ p → p ≤ 50 → scalarEnvelope p (slabRadius p) < cyclicConstant p := by
  intro p hp hp50
  unfold slabRadius
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact envelope_1 p hp h1
  · exact envelope_2 p (by linarith) h2
  · exact envelope_3 p (by linarith) h3
  · exact envelope_4 p (by linarith) h4
  · exact envelope_5 p (by linarith) h5
  · exact envelope_6_q37682 p (by linarith) h6
  · exact envelope_7 p (by linarith) h7
  · exact envelope_8 p (by linarith) hp50

end HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem solution : ∀ p : ℝ, 32 ≤ p → p ≤ 50 → scalarEnvelope p (slabRadius p) < cyclicConstant p := by
  exact HlawkaSchatten.DiagonalCutoff32.slab_envelopes32_local
