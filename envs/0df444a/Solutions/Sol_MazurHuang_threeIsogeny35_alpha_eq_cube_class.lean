-- Prove2me | solution 1 for MazurHuang.threeIsogeny35_alpha_eq_cube_class
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:07:22.304288+00:00
-- url     : https://prove2.me/submissions/54c87829-ea95-45f5-ad66-902ef6506be3

/-
First 3-descent on y^2 = x^3 + (4x+28)^2: the descent function takes values in three cube classes.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean (integral models, the 2-adic normalization, coprimality away from 7, short_alpha_cubeclass)
  * the published statement
-/
import Mathlib

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean. -/
section

namespace MazurProof.RationalPointsX135

noncomputable section

open scoped NumberField

open UniqueFactorizationMonoid

-- FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, lines 138-562
private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

private theorem den_monic_cubic_const (a b c : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2 + c * D ^ 3
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D + c * D ^ 2)) D :=
      h1.add_mul_left_left _
    convert h2 using 1 <;> ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

private theorem rat_denom_square_monic_const (a b c : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den = x.den ^ 3 := by
    exact_mod_cast den_monic_cubic_const a b c x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

theorem integral_model_monic_const (a b c : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      y = (C : ℚ) / (B : ℚ) ^ 3 ∧
      C ^ 2 = A ^ 3 + a * A ^ 2 * B ^ 2 + b * A * B ^ 4 + c * B ^ 6 := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ := rat_denom_square_monic_const a b c x y h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A ^ 3 + a * A ^ 2 * B ^ 2 + b * A * B ^ 4 + c * B ^ 6
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  have hsquares : (y * (B : ℚ) ^ 3) ^ 2 = (C : ℚ) ^ 2 := by
    rw [hrat]
    exact_mod_cast (show N = C ^ 2 by simpa [pow_two] using hC)
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with heq | heq
  · refine ⟨A, B, C, hBpos, hcop, hx, ?_, ?_⟩
    · apply (eq_div_iff (pow_ne_zero 3 hBne)).2
      simpa using heq
    · simpa [N, pow_two] using hC.symm
  · refine ⟨A, B, -C, hBpos, hcop, hx, ?_, ?_⟩
    · apply (eq_div_iff (pow_ne_zero 3 hBne)).2
      simpa using heq
    · simpa [N, pow_two] using hC.symm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem even_short_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 16 * A ^ 2 * B ^ 2 + 224 * A * B ^ 4 + 784 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            28 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            28 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide +kernel  -- port v4.33.1: kernel evaluation only (plain `decide` evaluates twice)

private theorem even_short_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 16 * A ^ 2 * B ^ 2 +
      224 * A * B ^ 4 + 784 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 4 * A * B - 28 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 4 * A * B + 28 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      16 * (A : ZMod 32) ^ 2 * B ^ 2 + 224 * (A : ZMod 32) * B ^ 4 +
        784 * (B : ZMod 32) ^ 6 := by
    have h' := congrArg (fun n : ℤ => (n : ZMod 32)) hmodel
    push_cast at h'
    exact h'
  have hA2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (A : ZMod 32) = 0 := by
    have hz : (A : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd A 2).mpr hA
    simpa [ZMod.castHom_apply] using hz
  have hB2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (B : ZMod 32) ≠ 0 := by
    intro hz
    apply hB
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp
    simpa [ZMod.castHom_apply] using hz
  have hc := even_short_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 4 * A * B - 28 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 4 * A * B + 28 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Integral coordinates on the rational flex model, normalized so that the
two factors of the descent function have only the prime seven in common. -/
theorem short_flex_integral_model {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (4 * x + 28) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 4 * M * D + 7 * D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((16 : ℤ) : ℚ) * x ^ 2 +
      ((224 : ℤ) : ℚ) * x + (784 : ℤ) := by
    norm_num at h ⊢
    exact h
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 16 224 784 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 4 * A * B - 28 * B ^ 3) *
          (C + 4 * A * B + 28 * B ^ 3) = A ^ 3 := by
    calc
      (C - 4 * A * B - 28 * B ^ 3) *
          (C + 4 * A * B + 28 * B ^ 3) =
          C ^ 2 - (4 * A * B + 28 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_short_model_divisibility hA2 (by
        rw [← even_iff_two_dvd]
        exact Int.not_even_iff_odd.mpr hBodd) hmodel
    obtain ⟨M, hM⟩ := hA4
    obtain ⟨R, hR⟩ := hN8
    obtain ⟨S, hS⟩ := hP8
    have hcopMD : IsCoprime M B := by
      rw [hM] at hcopI
      exact hcopI.of_mul_left_right
    have hprod : R * S = M ^ 3 := by
      rw [hR, hS, hM] at hprodRaw
      ring_nf at hprodRaw ⊢
      omega
    have hlin : S = R + 4 * M * B + 7 * B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 4 * M * B + 7 * B ^ 3) := by
        calc
          8 * S = C + 4 * A * B + 28 * B ^ 3 := hS.symm
          _ = (C - 4 * A * B - 28 * B ^ 3) +
              8 * (4 * M * B + 7 * B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (4 * M * B + 7 * B ^ 3) := by rw [hR]
          _ = 8 * (R + 4 * M * B + 7 * B ^ 3) := by ring
      omega
    refine ⟨M, B, R, S, hBpos,
      Int.isCoprime_iff_gcd_eq_one.mp hcopMD, ?_, ?_, hprod, hlin⟩
    · rw [hx, hM]
      push_cast
      ring
    · rw [hx, hy, hM]
      push_cast
      field_simp [hBneQ]
      have hR' := hR
      rw [hM] at hR'
      have hR'' := congrArg (fun n : ℤ => (n : ℚ)) hR'
      push_cast at hR''
      linear_combination hR''
  · have hcopA2 : IsCoprime A (2 : ℤ) :=
      Int.isCoprime_two_right.mpr hAodd
    have hcopAD : IsCoprime A (2 * B) := hcopA2.mul_right hcopI
    refine ⟨A, 2 * B, C - 4 * A * B - 28 * B ^ 3,
      C + 4 * A * B + 28 * B ^ 3, by positivity,
      Int.isCoprime_iff_gcd_eq_one.mp hcopAD, ?_, ?_, hprodRaw, ?_⟩
    · rw [hx]
      push_cast
      field_simp [hBneQ]
      ring
    · rw [hx, hy]
      push_cast
      field_simp [hBneQ]
      ring
    · ring

private theorem flex_common_prime_eq_seven
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 4 * M * D + 7 * D ^ 3)
    {p : ℕ} (hp : p.Prime) (hpR : (p : ℤ) ∣ R) (hpS : (p : ℤ) ∣ S) :
    p = 7 := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpPow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpPow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS hpR
  have hpSum : (p : ℤ) ∣ 4 * M * D + 7 * D ^ 3 := by
    rw [hlin] at hpDiff
    convert hpDiff using 1 <;> ring
  have hpFirst : (p : ℤ) ∣ 4 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨4 * k * D, ?_⟩
    rw [hk]
    ring
  have hpTail : (p : ℤ) ∣ 7 * D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    rcases this with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linear_combination hk
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hpD : ¬(p : ℤ) ∣ D := by
    intro hpD
    exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)
  rcases hpInt.dvd_mul.mp hpTail with hp7 | hpD3
  · have hp7Nat : p ∣ 7 := by exact_mod_cast hp7
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hp7Nat with hp1 | hp7'
    · exact (hp.ne_one hp1).elim
    · exact hp7'
  · exact (hpD (hpInt.dvd_of_dvd_pow hpD3)).elim

private theorem isCoprime_of_common_prime_eq_seven {R S : ℤ}
    (hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R → (p : ℤ) ∣ S → p = 7)
    (hnotBoth : ¬((7 : ℤ) ∣ R ∧ (7 : ℤ) ∣ S)) : IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hcop
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hp7 := hsupport hp hpR' hpS'
  subst p
  exact hnotBoth ⟨hpR', hpS'⟩

/-- The rational-flex descent function has one of the three cube classes
`1`, `7`, and `49`. -/
theorem flex_factor_cubeclass
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 4 * M * D + 7 * D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 ∨ R = 7 * q ^ 3 ∨ R = 49 * q ^ 3 := by
  have hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R → (p : ℤ) ∣ S → p = 7 :=
    fun {_p} hp hpR hpS => flex_common_prime_eq_seven hcop hprod hlin hp hpR hpS
  by_cases h7R : (7 : ℤ) ∣ R
  · have h7Mpow : (7 : ℤ) ∣ M ^ 3 := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left h7R S
    have h7M : (7 : ℤ) ∣ M :=
      Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7Mpow
    have h7S : (7 : ℤ) ∣ S := by
      rw [hlin]
      have hmid : (7 : ℤ) ∣ 4 * M * D := by
        rcases h7M with ⟨m, hm⟩
        refine ⟨4 * m * D, ?_⟩
        rw [hm]
        ring
      exact dvd_add (dvd_add h7R hmid) (dvd_mul_right 7 (D ^ 3))
    obtain ⟨R1, hR1⟩ := h7R
    obtain ⟨S1, hS1⟩ := h7S
    obtain ⟨M1, hM1⟩ := h7M
    have hprod1 : R1 * S1 = 7 * M1 ^ 3 := by
      rw [hR1, hS1, hM1] at hprod
      ring_nf at hprod ⊢
      omega
    have hlin1 : S1 = R1 + 4 * M1 * D + D ^ 3 := by
      rw [hR1, hS1, hM1] at hlin
      ring_nf at hlin ⊢
      omega
    have hnotBoth1 : ¬((7 : ℤ) ∣ R1 ∧ (7 : ℤ) ∣ S1) := by
      rintro ⟨h7R1, h7S1⟩
      obtain ⟨r, hr⟩ := h7R1
      obtain ⟨s, hs⟩ := h7S1
      have hM1cube : M1 ^ 3 = 7 * (r * s) := by
        rw [hr, hs] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have h7M1pow : (7 : ℤ) ∣ M1 ^ 3 := ⟨r * s, hM1cube⟩
      have h7M1 : (7 : ℤ) ∣ M1 :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7M1pow
      obtain ⟨m, hm⟩ := h7M1
      have hDcube : D ^ 3 = 7 * (s - r - 4 * m * D) := by
        rw [hr, hs, hm] at hlin1
        ring_nf at hlin1 ⊢
        omega
      have h7Dpow : (7 : ℤ) ∣ D ^ 3 := ⟨s - r - 4 * m * D, hDcube⟩
      have h7D : (7 : ℤ) ∣ D :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7Dpow
      have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have hu : IsUnit (7 : ℤ) :=
        hcopI.isUnit_of_dvd' (show (7 : ℤ) ∣ M by exact ⟨M1, hM1⟩) h7D
      rw [Int.isUnit_iff_abs_eq] at hu
      norm_num at hu
    have hcop1 : IsCoprime R1 S1 :=
      isCoprime_of_common_prime_eq_seven
        (fun {_p} hp hpR hpS => hsupport hp
          (hR1 ▸ dvd_mul_of_dvd_right hpR 7)
          (hS1 ▸ dvd_mul_of_dvd_right hpS 7)) hnotBoth1
    by_cases h7R1 : (7 : ℤ) ∣ R1
    · obtain ⟨R2, hR2⟩ := h7R1
      have hprod2 : R2 * S1 = M1 ^ 3 := by
        rw [hR2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R2 S1 := by
        rw [hR2] at hcop1
        exact hcop1.of_mul_left_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2 (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inr ?_)⟩
      rw [hR1, hR2, hq]
      ring
    · have h7S1 : (7 : ℤ) ∣ S1 := by
        have h7prod : (7 : ℤ) ∣ R1 * S1 := by rw [hprod1]; exact dvd_mul_right 7 _
        exact ((by norm_num : Prime (7 : ℤ)).dvd_mul.mp h7prod).resolve_left h7R1
      obtain ⟨S2, hS2⟩ := h7S1
      have hprod2 : R1 * S2 = M1 ^ 3 := by
        rw [hS2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R1 S2 := by
        rw [hS2] at hcop1
        exact hcop1.of_mul_right_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2 (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inl ?_)⟩
      rw [hR1, hq]
  · have hcopRS : IsCoprime R S :=
      isCoprime_of_common_prime_eq_seven hsupport (fun h => h7R h.1)
    obtain ⟨q, hq⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left hcopRS (show Odd 3 by decide) hprod
    exact ⟨q, Or.inl hq⟩

theorem short_alpha_cubeclass {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ r : ℚ,
      y - (4 * x + 28) = r ^ 3 ∨
      y - (4 * x + 28) = 7 * r ^ 3 ∨
      y - (4 * x + 28) = 49 * r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    short_flex_integral_model h
  obtain ⟨q, hq | hq | hq⟩ := flex_factor_cubeclass hcop hprod hlin
  all_goals
    refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  · left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; right
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring


end

end MazurProof.RationalPointsX135

end

theorem solution
    {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ r : ℚ,
      y - (4 * x + 28) = r ^ 3 ∨
      y - (4 * x + 28) = 7 * r ^ 3 ∨
      y - (4 * x + 28) = 49 * r ^ 3 :=
  MazurProof.RationalPointsX135.short_alpha_cubeclass h
