-- Prove2me | solution 1 for MazurHuang.X0_five_seven_fiber_inverse_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:08:50.923154+00:00
-- url     : https://prove2.me/submissions/76cd1ef5-c753-4f59-a6b0-a2f58bc44311

/-
The inverse map from the fibre product X_0(5) x_j X_0(7) is defined away from b = 0.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (the fibre equation, inverseXDen, inverseXNum, the three factors without rational roots, the
    two Bezout identities, inverseXDen_ne_zero, inverseXNum_ne_zero)
  * the published statement
-/
import Mathlib

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 23-32
/-- The standard `X₀(5)` numerator in its Hauptmodul `a`. -/
def J5Numerator (a : ℚ) : ℚ := (a ^ 2 + 10 * a + 5) ^ 3

/-- The standard `X₀(7)` numerator in its Hauptmodul `b`. -/
def J7Numerator (b : ℚ) : ℚ :=
  (b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3

/-- The affine fiber product `X₀(5) ×_j X₀(7)`. -/
def X035FiberEquation (a b : ℚ) : Prop :=
  b * J5Numerator a = a * J7Numerator b

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 123-131
def inverseXDen (a b : ℚ) : ℚ :=
  347 * b + 384 * b ^ 2 + 133 * b ^ 3 + 19 * b ^ 4 + b ^ 5 - 136 * a -
    15 * a * b + 4 * a * b ^ 2 - 51 * a ^ 2 - 8 * a ^ 2 * b +
    a ^ 2 * b ^ 2 - 4 * a ^ 3 - a ^ 3 * b

def inverseXNum (a b : ℚ) : ℚ :=
  3 - 74 * b - 63 * b ^ 2 - 14 * b ^ 3 - b ^ 4 + 23 * a - 54 * a * b -
    63 * a * b ^ 2 - 14 * a * b ^ 3 - a * b ^ 4 + 4 * a ^ 2 +
    4 * a ^ 2 * b

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 191-358
private def fiberFactorTwo (b : ℚ) : ℚ := b ^ 2 + 5 * b + 1

private def fiberFactorFour (b : ℚ) : ℚ :=
  b ^ 4 + 14 * b ^ 3 + 63 * b ^ 2 + 70 * b - 7

private def fiberFactorFive (b : ℚ) : ℚ :=
  b ^ 5 + 26 * b ^ 4 + 267 * b ^ 3 + 1338 * b ^ 2 + 3233 * b + 3072

private theorem fiberFactorTwo_ne_zero (b : ℚ) : fiberFactorTwo b ≠ 0 := by
  intro h
  have hsquare : (2 * b + 5) ^ 2 = 21 := by
    unfold fiberFactorTwo at h
    nlinarith
  have hnot : ¬ IsSquare (21 : ℚ) := by norm_num
  exact hnot ⟨2 * b + 5, by simpa [pow_two] using hsquare.symm⟩

private theorem int_dvd_seven_cases {z : ℤ} (hz : z ∣ (7 : ℤ)) :
    z = 1 ∨ z = -1 ∨ z = 7 ∨ z = -7 := by
  have habs : z.natAbs ∣ 7 := (Int.natAbs_dvd_natAbs).mpr hz
  have habsCases : z.natAbs = 1 ∨ z.natAbs = 7 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp habs
  rcases habsCases with h1 | h7
  · rcases Int.natAbs_eq_iff.mp h1 with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
  · rcases Int.natAbs_eq_iff.mp h7 with hz | hz
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))

private theorem fiberFactorFour_ne_zero (b : ℚ) : fiberFactorFour b ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 4 + C 14 * X ^ 3 + C 63 * X ^ 2 + C 70 * X - C 7
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval b p = 0 := by
    simp [p, aeval_def]
    unfold fiberFactorFour at h
    norm_cast
  obtain ⟨z, hb, hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  have hz7 : z ∣ (7 : ℤ) := by
    simpa [p] using hzdiv
  rcases int_dvd_seven_cases hz7 with rfl | rfl | rfl | rfl <;>
    rw [hb] at h <;> norm_num [fiberFactorFour] at h

private theorem fiberFactorFive_ne_zero (b : ℚ) : fiberFactorFive b ≠ 0 := by
  intro h
  let p : ℤ[X] :=
    X ^ 5 + C 26 * X ^ 4 + C 267 * X ^ 3 + C 1338 * X ^ 2 +
      C 3233 * X + C 3072
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval b p = 0 := by
    simp [p, aeval_def]
    unfold fiberFactorFive at h
    norm_cast
  obtain ⟨z, hb, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hb] at h
  unfold fiberFactorFive at h
  have hz : z ^ 5 + 26 * z ^ 4 + 267 * z ^ 3 + 1338 * z ^ 2 +
      3233 * z + 3072 = 0 := by
    have hzcast : ((z ^ 5 + 26 * z ^ 4 + 267 * z ^ 3 + 1338 * z ^ 2 +
        3233 * z + 3072 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 7) ^ 5 + 26 * (z : ZMod 7) ^ 4 +
      267 * (z : ZMod 7) ^ 3 + 1338 * (z : ZMod 7) ^ 2 +
      3233 * (z : ZMod 7) + 3072 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 7)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ t : ZMod 7,
    t ^ 5 + 26 * t ^ 4 + 267 * t ^ 3 + 1338 * t ^ 2 +
      3233 * t + 3072 ≠ 0) (z : ZMod 7) hzmod

private def inverseDenBezoutFiber (a b : ℚ) : ℚ :=
  (((-6823936) + a * ((-2558976) + a * (-200704))) + b * (((-16179800) + a * ((-4250593) + a * (-311916))) + b *
  (((-16869850) + a * ((-3164821) + a * (-212807))) + b * (((-10242635) + a * ((-1390468) + a * (-84107))) + b *
  (((-4022705) + a * ((-397759) + a * (-21508))) + b * (((-1069876) + a * ((-76100) + a * (-3735))) + b *
  (((-195367) + a * ((-9451) + a * (-436))) + b * (((-24212) + a * ((-687) + a * (-31))) + b * (((-1953) + a *
  ((-22) + a * (-1))) + b * ((-93) + b * (-2)))))))))))

private def inverseDenBezoutDen (a b : ℚ) : ℚ :=
  (2458624 + b * ((3105963 + a * ((-79027200) + a * ((-65228800) + a * ((-15805440) + a * ((-1505280) + a *
  (-50176)))))) + b * ((1634709 + a * ((-269473373) + a * ((-125386268) + a * ((-24452025) + a * ((-2091050) + a
  * (-65435)))))) + b * ((491215 + a * ((-384215042) + a * ((-111718295) + a * ((-17071150) + a * ((-1276421) +
  a * (-36843)))))) + b * ((2736845 + a * ((-313697015) + a * ((-60456951) + a * ((-7085762) + a * ((-451333) +
  a * (-11816)))))) + b * ((11466471 + a * ((-166708511) + a * ((-21935030) + a * ((-1929598) + a * ((-102602) +
  a * (-2423)))))) + b * ((18487238 + a * ((-61600100) + a * ((-5585720) + a * ((-353917) + a * ((-15313) + a *
  (-328)))))) + b * ((16047959 + a * ((-16387752) + a * ((-1024899) + a * ((-42902) + a * ((-1410) + a *
  (-27)))))) + b * ((8642167 + a * ((-3180742) + a * ((-138029) + a * ((-3268) + a * ((-67) + a * (-1)))))) + b
  * ((3090520 + a * ((-447616) + a * ((-13724) + a * ((-144) + a * (-1))))) + b * ((757849 + a * ((-44424) + a *
  ((-978) + a * (-3)))) + b * ((128501 + a * ((-2935) + a * (-45))) + b * ((14860 + a * ((-115) + a * (-1))) + b
  * ((1122 + a * (-2)) + b * (50 + b * 1)))))))))))))))

private def inverseNumBezoutFiber (a b : ℚ) : ℚ :=
  ((23552 + a * 4096) + b * (((-107059) + a * (-8324)) + b * (((-2631) + a * (-39664)) + b * ((490475 + a *
  (-46340)) + b * ((718402 + a * (-25620)) + b * ((488297 + a * (-7700)) + b * ((192939 + a * (-1284)) + b *
  ((47677 + a * (-112)) + b * ((7506 + a * (-4)) + b * (735 + b * (41 + b * 1)))))))))))

private def inverseNumBezoutNum (a b : ℚ) : ℚ :=
  (50176 + b * ((58267 + a * ((-1478544) + a * ((-1312576) + a * ((-321792) + a * ((-30720) + a * (-1024)))))) +
  b * (((-315074) + a * ((-33471) + a * (2657942 + a * (836894 + a * (88237 + a * 3105))))) + b * (((-13651965)
  + a * (2558427 + a * (6631538 + a * (1919914 + a * (196527 + a * 6811))))) + b * (((-58725555) + a * (2162790
  + a * (4777220 + a * (1359092 + a * (138222 + a * 4774))))) + b * (((-101447146) + a * (759375 + a * (1648682
  + a * (466018 + a * (47283 + a * 1631))))) + b * (((-96844908) + a * (128358 + a * (298052 + a * (84084 + a *
  (8526 + a * 294))))) + b * (((-58457974) + a * (9563 + a * (27378 + a * (7722 + a * (783 + a * 27))))) + b *
  (((-23885992) + a * (97 + a * (1014 + a * (286 + a * (29 + a * 1))))) + b * (((-6845465) + a * (-16)) + b *
  ((-1396874) + b * ((-202601) + b * ((-20465) + b * ((-1372) + b * ((-55) + b * (-1))))))))))))))))

set_option maxHeartbeats 0 in
private theorem inverseDenBezoutIdentity (a b : ℚ) :
    inverseDenBezoutFiber a b *
          (b * J5Numerator a - a * J7Numerator b) +
        inverseDenBezoutDen a b * inverseXDen a b =
      b * fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 * fiberFactorFive b := by
  unfold inverseDenBezoutFiber inverseDenBezoutDen inverseXDen
    J5Numerator J7Numerator fiberFactorTwo fiberFactorFour fiberFactorFive
  ring

set_option maxHeartbeats 0 in
private theorem inverseNumBezoutIdentity (a b : ℚ) :
    inverseNumBezoutFiber a b *
          (b * J5Numerator a - a * J7Numerator b) +
        inverseNumBezoutNum a b * inverseXNum a b =
      fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 * fiberFactorFive b := by
  unfold inverseNumBezoutFiber inverseNumBezoutNum inverseXNum
    J5Numerator J7Numerator fiberFactorTwo fiberFactorFour fiberFactorFive
  ring

theorem inverseXDen_ne_zero {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) : inverseXDen a b ≠ 0 := by
  intro hd
  have hi := inverseDenBezoutIdentity a b
  have hf : b * J5Numerator a - a * J7Numerator b = 0 :=
    sub_eq_zero.mpr h
  rw [hf, hd] at hi
  simp only [mul_zero, zero_add] at hi
  have hrhs :
      b * fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 *
          fiberFactorFive b ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hb (pow_ne_zero 3 (fiberFactorTwo_ne_zero b)))
        (pow_ne_zero 2 (fiberFactorFour_ne_zero b)))
      (fiberFactorFive_ne_zero b)
  exact hrhs hi.symm

theorem inverseXNum_ne_zero {a b : ℚ}
    (h : X035FiberEquation a b) : inverseXNum a b ≠ 0 := by
  intro hn
  have hi := inverseNumBezoutIdentity a b
  have hf : b * J5Numerator a - a * J7Numerator b = 0 :=
    sub_eq_zero.mpr h
  rw [hf, hn] at hi
  simp only [mul_zero, zero_add] at hi
  have hrhs :
      fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 *
          fiberFactorFive b ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (pow_ne_zero 3 (fiberFactorTwo_ne_zero b))
        (pow_ne_zero 2 (fiberFactorFour_ne_zero b)))
      (fiberFactorFive_ne_zero b)
  exact hrhs hi.symm


end

end MazurProof.RationalPointsX135

end

theorem solution
    {a b : ℚ}
    (h : b * (a ^ 2 + 10 * a + 5) ^ 3 = a * ((b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3)) :
    3 - 74 * b - 63 * b ^ 2 - 14 * b ^ 3 - b ^ 4 + 23 * a - 54 * a * b -
        63 * a * b ^ 2 - 14 * a * b ^ 3 - a * b ^ 4 + 4 * a ^ 2 +
        4 * a ^ 2 * b ≠ 0 ∧
      (b ≠ 0 →
        347 * b + 384 * b ^ 2 + 133 * b ^ 3 + 19 * b ^ 4 + b ^ 5 - 136 * a -
        15 * a * b + 4 * a * b ^ 2 - 51 * a ^ 2 - 8 * a ^ 2 * b +
        a ^ 2 * b ^ 2 - 4 * a ^ 3 - a ^ 3 * b ≠ 0) :=
  ⟨MazurProof.RationalPointsX135.inverseXNum_ne_zero h,
    fun hb => MazurProof.RationalPointsX135.inverseXDen_ne_zero hb h⟩
