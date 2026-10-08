-- Prove2me | solution 1 for MazurHuang.N19.good_flex_cubeclasses
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:19:28.587986+00:00
-- url     : https://prove2.me/submissions/58e15fd3-de41-490a-9a8e-151422ae21a4

/-
Cubeclasses of the rational good-model flex function
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_MazurHuang_N19_good_even_model_mod_thirtytwo


-- Source FLT/Assumptions/MazurProof/XDelta19GoodModel.lean:30-61; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodModel
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
/-- The integral model in the middle of the conductor-nineteen
three-isogeny chain. -/
def goodCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 64
  a₃ := 0
  a₄ := 1216
  a₆ := 5776

/-- The affine equation of the good integral model. -/
def OnGood (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2

/-- The good model has discriminant `-2^12 * 19^3`, hence in particular
good reduction at three. -/
theorem goodCurve_delta : goodCurve.Δ = (-28094464 : ℚ) := by
  norm_num [goodCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The good integral model is nonsingular. -/
instance goodCurve_isElliptic : goodCurve.IsElliptic where
  isUnit := by
    rw [goodCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed good equation. -/
@[simp] theorem goodCurve_equation_iff (x y : ℚ) :
    Equation goodCurve x y ↔ OnGood x y := by
  rw [equation_iff]
  simp [goodCurve, OnGood]
  ring_nf

end
end MazurProof.XDelta19GoodModel
end

namespace MazurProof.XDelta19GoodModel
abbrev GoodPoint := WeierstrassCurve.Affine.Point goodCurve
end MazurProof.XDelta19GoodModel

-- Source FLT/Assumptions/MazurProof/XDelta19GoodModel.lean:153-170; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodModel
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
/-- Nonsingularity of the positive visible flex. -/
theorem goodT_nonsingular : Nonsingular goodCurve (0 : ℚ) 76 :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 76).mpr (by norm_num [OnGood])

/-- Nonsingularity of the negative visible flex. -/
theorem goodTNeg_nonsingular : Nonsingular goodCurve (0 : ℚ) (-76) :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 (-76)).mpr (by norm_num [OnGood])

/-- The positive rational flex on the good model. -/
def goodT : GoodPoint :=
  Point.some 0 76 goodT_nonsingular

/-- The negative rational flex on the good model. -/
def goodTNeg : GoodPoint :=
  Point.some 0 (-76) goodTNeg_nonsingular

end
end MazurProof.XDelta19GoodModel
end

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

namespace MazurProof.XDelta19GoodDescent
private theorem even_good_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 + 1216 * A * B ^ 4 +
          5776 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) :=
  MazurHuang.N19.good_even_model_mod_thirtytwo
end MazurProof.XDelta19GoodDescent

-- Source FLT/Assumptions/MazurProof/XDelta19GoodDescent.lean:48-369; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodDescent
open MazurProof.RationalPointsX135 MazurProof.XDelta19GoodModel
noncomputable section
/-- The finite two-adic certificate lifts to the required integer
divisibilities. -/
private theorem even_good_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 +
      1216 * A * B ^ 4 + 5776 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 8 * A * B - 76 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 8 * A * B + 76 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      64 * (A : ZMod 32) ^ 2 * B ^ 2 +
      1216 * (A : ZMod 32) * B ^ 4 + 5776 * (B : ZMod 32) ^ 6 := by
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
  have hc := even_good_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 8 * A * B - 76 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 8 * A * B + 76 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Primitive integral flex coordinates in which the two descent factors
have cube product and can share only the prime nineteen. -/
theorem good_flex_integral_model {x y : ℚ}
    (h : OnGood x y) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (8 * x + 76) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 8 * M * D + 19 * D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((64 : ℤ) : ℚ) * x ^ 2 +
      ((1216 : ℤ) : ℚ) * x + (5776 : ℤ) := by
    unfold OnGood at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 64 1216 5776 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 8 * A * B - 76 * B ^ 3) *
          (C + 8 * A * B + 76 * B ^ 3) = A ^ 3 := by
    calc
      (C - 8 * A * B - 76 * B ^ 3) *
          (C + 8 * A * B + 76 * B ^ 3) =
          C ^ 2 - (8 * A * B + 76 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_good_model_divisibility hA2 (by
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
    have hlin : S = R + 8 * M * B + 19 * B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 8 * M * B + 19 * B ^ 3) := by
        calc
          8 * S = C + 8 * A * B + 76 * B ^ 3 := hS.symm
          _ = (C - 8 * A * B - 76 * B ^ 3) +
              8 * (8 * M * B + 19 * B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (8 * M * B + 19 * B ^ 3) := by rw [hR]
          _ = 8 * (R + 8 * M * B + 19 * B ^ 3) := by ring
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
    refine ⟨A, 2 * B, C - 8 * A * B - 76 * B ^ 3,
      C + 8 * A * B + 76 * B ^ 3, by positivity,
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

/-! ## The three possible cubeclasses -/

/-- A prime common to both normalized descent factors must be nineteen. -/
private theorem flex_common_prime_eq_nineteen
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 8 * M * D + 19 * D ^ 3)
    {p : ℕ} (hp : p.Prime) (hpR : (p : ℤ) ∣ R)
    (hpS : (p : ℤ) ∣ S) :
    p = 19 := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpPow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpPow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS hpR
  have hpSum : (p : ℤ) ∣ 8 * M * D + 19 * D ^ 3 := by
    rw [hlin] at hpDiff
    have heq :
        (R + 8 * M * D + 19 * D ^ 3) - R =
          8 * M * D + 19 * D ^ 3 := by ring
    rwa [heq] at hpDiff
  have hpFirst : (p : ℤ) ∣ 8 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨8 * k * D, ?_⟩
    rw [hk]
    ring
  have hpTail : (p : ℤ) ∣ 19 * D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    rcases this with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linear_combination hk
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hpD : ¬(p : ℤ) ∣ D := by
    intro hpD
    exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)
  rcases hpInt.dvd_mul.mp hpTail with hp19 | hpD3
  · have hp19Nat : p ∣ 19 := by exact_mod_cast hp19
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp hp19Nat with
      hp1 | hp19'
    · exact (hp.ne_one hp1).elim
    · exact hp19'
  · exact (hpD (hpInt.dvd_of_dvd_pow hpD3)).elim

/-- If nineteen is not a common factor, the two normalized descent
factors are coprime. -/
private theorem isCoprime_of_common_prime_eq_nineteen {R S : ℤ}
    (hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R →
      (p : ℤ) ∣ S → p = 19)
    (hnotBoth : ¬((19 : ℤ) ∣ R ∧ (19 : ℤ) ∣ S)) :
    IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hcop
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hp19 := hsupport hp hpR' hpS'
  subst p
  exact hnotBoth ⟨hpR', hpS'⟩

/-- The normalized first descent factor has cubeclass `1`, `19`, or
`19²`. -/
theorem flex_factor_cubeclass
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 8 * M * D + 19 * D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 ∨ R = 19 * q ^ 3 ∨ R = 361 * q ^ 3 := by
  have hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R →
      (p : ℤ) ∣ S → p = 19 :=
    fun {_p} hp hpR hpS =>
      flex_common_prime_eq_nineteen hcop hprod hlin hp hpR hpS
  by_cases h19R : (19 : ℤ) ∣ R
  · have h19Mpow : (19 : ℤ) ∣ M ^ 3 := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left h19R S
    have h19M : (19 : ℤ) ∣ M :=
      Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19Mpow
    have h19S : (19 : ℤ) ∣ S := by
      rw [hlin]
      have hmid : (19 : ℤ) ∣ 8 * M * D := by
        rcases h19M with ⟨m, hm⟩
        refine ⟨8 * m * D, ?_⟩
        rw [hm]
        ring
      exact dvd_add (dvd_add h19R hmid) (dvd_mul_right 19 (D ^ 3))
    obtain ⟨R1, hR1⟩ := h19R
    obtain ⟨S1, hS1⟩ := h19S
    obtain ⟨M1, hM1⟩ := h19M
    have hprod1 : R1 * S1 = 19 * M1 ^ 3 := by
      rw [hR1, hS1, hM1] at hprod
      ring_nf at hprod ⊢
      omega
    have hlin1 : S1 = R1 + 8 * M1 * D + D ^ 3 := by
      rw [hR1, hS1, hM1] at hlin
      ring_nf at hlin ⊢
      omega
    have hnotBoth1 : ¬((19 : ℤ) ∣ R1 ∧ (19 : ℤ) ∣ S1) := by
      rintro ⟨h19R1, h19S1⟩
      obtain ⟨r, hr⟩ := h19R1
      obtain ⟨s, hs⟩ := h19S1
      have hM1cube : M1 ^ 3 = 19 * (r * s) := by
        rw [hr, hs] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have h19M1pow : (19 : ℤ) ∣ M1 ^ 3 := ⟨r * s, hM1cube⟩
      have h19M1 : (19 : ℤ) ∣ M1 :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19M1pow
      obtain ⟨m, hm⟩ := h19M1
      have hDcube : D ^ 3 = 19 * (s - r - 8 * m * D) := by
        rw [hr, hs, hm] at hlin1
        ring_nf at hlin1 ⊢
        omega
      have h19Dpow : (19 : ℤ) ∣ D ^ 3 :=
        ⟨s - r - 8 * m * D, hDcube⟩
      have h19D : (19 : ℤ) ∣ D :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 19) h19Dpow
      have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have hu : IsUnit (19 : ℤ) :=
        hcopI.isUnit_of_dvd'
          (show (19 : ℤ) ∣ M by exact ⟨M1, hM1⟩) h19D
      rw [Int.isUnit_iff_abs_eq] at hu
      norm_num at hu
    have hcop1 : IsCoprime R1 S1 :=
      isCoprime_of_common_prime_eq_nineteen
        (fun {_p} hp hpR hpS => hsupport hp
          (hR1 ▸ dvd_mul_of_dvd_right hpR 19)
          (hS1 ▸ dvd_mul_of_dvd_right hpS 19)) hnotBoth1
    by_cases h19R1 : (19 : ℤ) ∣ R1
    · obtain ⟨R2, hR2⟩ := h19R1
      have hprod2 : R2 * S1 = M1 ^ 3 := by
        rw [hR2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R2 S1 := by
        rw [hR2] at hcop1
        exact hcop1.of_mul_left_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2
          (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inr ?_)⟩
      rw [hR1, hR2, hq]
      ring
    · have h19S1 : (19 : ℤ) ∣ S1 := by
        have h19prod : (19 : ℤ) ∣ R1 * S1 := by
          rw [hprod1]
          exact dvd_mul_right 19 _
        have hor : (19 : ℤ) ∣ R1 ∨ (19 : ℤ) ∣ S1 :=
          (by norm_num : Prime (19 : ℤ)).dvd_mul.mp h19prod
        exact Or.resolve_left hor h19R1
      obtain ⟨S2, hS2⟩ := h19S1
      have hprod2 : R1 * S2 = M1 ^ 3 := by
        rw [hS2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R1 S2 := by
        rw [hS2] at hcop1
        exact hcop1.of_mul_right_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2
          (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inl ?_)⟩
      rw [hR1, hq]
  · have hcopRS : IsCoprime R S :=
      isCoprime_of_common_prime_eq_nineteen hsupport
        (fun h => h19R h.1)
    obtain ⟨q, hq⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left hcopRS
        (show Odd 3 by decide) hprod
    exact ⟨q, Or.inl hq⟩

/-- The rational flex function on the good model has exactly one of the
three candidate cubeclasses `1`, `19`, and `19²`. -/
theorem good_alpha_cubeclass {x y : ℚ} (h : OnGood x y) :
    ∃ r : ℚ,
      y - (8 * x + 76) = r ^ 3 ∨
      y - (8 * x + 76) = 19 * r ^ 3 ∨
      y - (8 * x + 76) = 361 * r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    good_flex_integral_model h
  obtain ⟨q, hq | hq | hq⟩ :=
    flex_factor_cubeclass hcop hprod hlin
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
end MazurProof.XDelta19GoodDescent
end

theorem solution {x y : ℚ} (h : y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2) :
    ∃ r : ℚ, y - (8 * x + 76) = r ^ 3 ∨ y - (8 * x + 76) = 19 * r ^ 3 ∨ y - (8 * x + 76) = 361 * r ^ 3 := by
  exact MazurProof.XDelta19GoodDescent.good_alpha_cubeclass h
