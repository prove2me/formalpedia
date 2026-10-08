-- Prove2me | solution 1 for MazurHuang.N19.short_flex_factor_is_rational_cube
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:38:31.258975+00:00
-- url     : https://prove2.me/submissions/e815b9aa-e453-4a1b-bf35-51ec1cb9521f

/-
The short-model flex factor is a rational cube
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_MazurHuang_N19_short_model_two_adic_certificate


-- Source FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean:138-250; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.RationalPointsX135
noncomputable section
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
end
end MazurProof.RationalPointsX135
end

namespace MazurProof.XDelta19Descent
open MazurProof.RationalPointsX135
noncomputable section
def OnShort (x y : ℚ) : Prop := y ^ 2 = x ^ 3 + (2*x+4)^2
private theorem even_short_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 + 16 * A * B ^ 4 +
          16 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  intro A B C hA hB
  exact MazurHuang.N19.short_model_two_adic_certificate A hA B hB C
/-- The finite certificate lifts to the required integer divisibilities. -/
private theorem even_short_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 +
      16 * A * B ^ 4 + 16 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 2 * A * B - 4 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 2 * A * B + 4 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      4 * (A : ZMod 32) ^ 2 * B ^ 2 + 16 * (A : ZMod 32) * B ^ 4 +
        16 * (B : ZMod 32) ^ 6 := by
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
      (C - 2 * A * B - 4 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 2 * A * B + 4 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Primitive integral flex coordinates in which the two descent factors are
coprime and have cube product. -/
theorem short_flex_integral_model {x y : ℚ}
    (h : OnShort x y) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (2 * x + 4) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 2 * M * D + D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((4 : ℤ) : ℚ) * x ^ 2 +
      ((16 : ℤ) : ℚ) * x + (16 : ℤ) := by
    unfold OnShort at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 4 16 16 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 2 * A * B - 4 * B ^ 3) *
          (C + 2 * A * B + 4 * B ^ 3) = A ^ 3 := by
    calc
      (C - 2 * A * B - 4 * B ^ 3) *
          (C + 2 * A * B + 4 * B ^ 3) =
          C ^ 2 - (2 * A * B + 4 * B ^ 3) ^ 2 := by ring
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
    have hlin : S = R + 2 * M * B + B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 2 * M * B + B ^ 3) := by
        calc
          8 * S = C + 2 * A * B + 4 * B ^ 3 := hS.symm
          _ = (C - 2 * A * B - 4 * B ^ 3) +
              8 * (2 * M * B + B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (2 * M * B + B ^ 3) := by rw [hR]
          _ = 8 * (R + 2 * M * B + B ^ 3) := by ring
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
    refine ⟨A, 2 * B, C - 2 * A * B - 4 * B ^ 3,
      C + 2 * A * B + 4 * B ^ 3, by positivity,
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

/-- No prime can divide both normalized descent factors. -/
private theorem flex_factors_isCoprime
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 2 * M * D + D ^ 3) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpMpow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR' S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpMpow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS' hpR'
  have hpSum : (p : ℤ) ∣ 2 * M * D + D ^ 3 := by
    rw [hlin] at hpDiff
    have hdiff :
        (R + 2 * M * D + D ^ 3) - R = 2 * M * D + D ^ 3 := by ring
    rwa [hdiff] at hpDiff
  have hpFirst : (p : ℤ) ∣ 2 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨2 * k * D, ?_⟩
    rw [hk]
    ring
  have hpDpow : (p : ℤ) ∣ D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    have hdiff :
        (2 * M * D + D ^ 3) - 2 * M * D = D ^ 3 := by ring
    rwa [hdiff] at this
  have hpD : (p : ℤ) ∣ D := hpInt.dvd_of_dvd_pow hpDpow
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)

/-- The normalized first descent factor is an integral cube. -/
theorem flex_factor_is_cube
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 2 * M * D + D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 := by
  have hcopRS : IsCoprime R S :=
    flex_factors_isCoprime hcop hprod hlin
  exact Int.eq_pow_of_mul_eq_pow_odd_left hcopRS
    (show Odd 3 by decide) hprod

/-- The first rational flex factor on the short model is always a rational
cube. -/
theorem short_alpha_is_cube {x y : ℚ} (h : OnShort x y) :
    ∃ r : ℚ, y - (2 * x + 4) = r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    short_flex_integral_model h
  obtain ⟨q, hq⟩ := flex_factor_is_cube hcop hprod hlin
  refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  rw [halpha, hq]
  push_cast
  field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
  ring

end
end MazurProof.XDelta19Descent

theorem solution {x y : ℚ} (h : y ^ 2 = x ^ 3 + (2 * x + 4) ^ 2) : ∃ r : ℚ, y - (2 * x + 4) = r ^ 3 := MazurProof.XDelta19Descent.short_alpha_is_cube h
