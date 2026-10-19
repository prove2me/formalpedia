-- Prove2me | solution 1 for MazurTransfer.order13_reflection_coordinate_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:05:06.697709+00:00
-- url     : https://prove2.me/submissions/76ff62bd-3f90-4275-b3bf-ddf74659a8ef

import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit reflection identities for the literal order-13
sextic, with every coefficient parameter and denominator hypothesis stated.
Named downstream consumer: the actual curve function-field reflection and
its arithmetic intertwiner for the cyclotomic quotient kernel.
-/

noncomputable section
universe u
namespace MazurTransfer.ReflectionCoordinateProofHelpers20261018
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13PellChartCertificate
variable {F : Type u} [Field F]

theorem scalar_certificate (t : F) :
    (3 * t - 1) * reflectionCubic t + (-3 * t ^ 2 - 8 * t + 12) * reflectionScalar t = 13 := by
  dsimp [reflectionCubic, reflectionScalar]
  ring

theorem scalar_ne_zero [CharZero F] (t : F) (ht : reflectionCubic t = 0) :
    reflectionScalar t ≠ 0 := by
  intro hD
  have h := scalar_certificate t
  rw [ht, hD] at h
  norm_num at h

theorem cleared_sextic_identity (t x : F) :
    (t - x) ^ 6 + 2 * (t - x) ^ 5 * reflectionDenominator t x +
      (t - x) ^ 4 * reflectionDenominator t x ^ 2 +
      2 * (t - x) ^ 3 * reflectionDenominator t x ^ 3 +
      6 * (t - x) ^ 2 * reflectionDenominator t x ^ 4 +
      4 * (t - x) * reflectionDenominator t x ^ 5 + reflectionDenominator t x ^ 6 =
    reflectionScalar t ^ 3 * sextic x - reflectionCubic t *
      (-2 * t * x - t + x ^ 2 - 1) * (t * x ^ 2 - t + x ^ 2 + 2 * x) *
      (t * x ^ 2 + 2 * t * x + 2 * x + 1) := by
  dsimp [reflectionDenominator, reflectionScalar, reflectionCubic, sextic]
  ring

theorem covariance (t x : F) (ht : reflectionCubic t = 0)
    (hx : reflectionDenominator t x ≠ 0) :
    reflectionDenominator t x ^ 6 * sextic (reflectionX t x) =
      reflectionScalar t ^ 3 * sextic x := by
  have h := cleared_sextic_identity t x
  rw [ht] at h
  simp only [zero_mul, sub_zero] at h
  dsimp [sextic] at h
  dsimp [reflectionX, sextic]
  field_simp [hx]
  convert h using 1 <;> ring

theorem preserves_curve (t s x y : F) (ht : reflectionCubic t = 0)
    (hs : s ^ 2 = reflectionScalar t) (hx : reflectionDenominator t x ≠ 0)
    (hy : y ^ 2 = sextic x) :
    reflectionY t s x y ^ 2 = sextic (reflectionX t x) := by
  have h := covariance t x ht hx
  have hs6 : s ^ 6 = reflectionScalar t ^ 3 := by
    calc
      _ = (s ^ 2) ^ 3 := by ring
      _ = _ := by rw [hs]
  dsimp [reflectionY]
  field_simp [hx]
  rw [hs6, hy]
  exact h.symm

theorem denominator_reflection (t x : F) (hx : reflectionDenominator t x ≠ 0) :
    reflectionDenominator t (reflectionX t x) =
      reflectionScalar t / reflectionDenominator t x := by
  dsimp [reflectionDenominator, reflectionX, reflectionScalar] at hx ⊢
  field_simp [hx]
  ring

theorem denominator_reflection_ne_zero (t x : F)
    (hD : reflectionScalar t ≠ 0) (hx : reflectionDenominator t x ≠ 0) :
    reflectionDenominator t (reflectionX t x) ≠ 0 := by
  rw [denominator_reflection t x hx]
  exact div_ne_zero hD hx

theorem reflectionX_involution (t x : F) (hD : reflectionScalar t ≠ 0)
    (hx : reflectionDenominator t x ≠ 0) :
    reflectionX t (reflectionX t x) = x := by
  change (t - reflectionX t x) / reflectionDenominator t (reflectionX t x) = x
  rw [denominator_reflection t x hx]
  have hn : t - reflectionX t x =
      x * reflectionScalar t / reflectionDenominator t x := by
    apply (eq_div_iff hx).mpr
    dsimp [reflectionX]
    rw [sub_mul, div_mul_cancel₀ _ hx]
    dsimp [reflectionDenominator, reflectionScalar]
    ring
  rw [hn]
  rw [div_div_div_cancel_right₀ hx, mul_div_cancel_right₀ _ hD]

theorem reflectionY_involution (t s x y : F) (hs : s ^ 2 = reflectionScalar t)
    (hD : reflectionScalar t ≠ 0) (hx : reflectionDenominator t x ≠ 0) :
    reflectionY t s (reflectionX t x) (reflectionY t s x y) = y := by
  have hs6 : s ^ 6 = reflectionScalar t ^ 3 := by
    calc
      _ = (s ^ 2) ^ 3 := by ring
      _ = _ := by rw [hs]
  unfold reflectionY
  rw [denominator_reflection t x hx]
  field_simp [hx, hD]
  rw [hs6]
  ring

end MazurTransfer.ReflectionCoordinateProofHelpers20261018
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13PellChartCertificate

theorem solution :
    (∀ {F : Type u} [Field F] (t s x y : F) (ht : reflectionCubic t = 0)
    (hs : s ^ 2 = reflectionScalar t) (hx : reflectionDenominator t x ≠ 0)
    (hy : y ^ 2 = sextic x),
    reflectionY t s x y ^ 2 = sextic (reflectionX t x)) ∧
      (∀ {F : Type u} [Field F] (t x : F) (hD : reflectionScalar t ≠ 0)
    (hx : reflectionDenominator t x ≠ 0),
    reflectionX t (reflectionX t x) = x) ∧
      (∀ {F : Type u} [Field F] (t s x y : F) (hs : s ^ 2 = reflectionScalar t)
    (hD : reflectionScalar t ≠ 0) (hx : reflectionDenominator t x ≠ 0),
    reflectionY t s (reflectionX t x) (reflectionY t s x y) = y) := by
  exact ⟨@MazurTransfer.ReflectionCoordinateProofHelpers20261018.preserves_curve,
    @MazurTransfer.ReflectionCoordinateProofHelpers20261018.reflectionX_involution,
    @MazurTransfer.ReflectionCoordinateProofHelpers20261018.reflectionY_involution⟩
#print axioms solution
