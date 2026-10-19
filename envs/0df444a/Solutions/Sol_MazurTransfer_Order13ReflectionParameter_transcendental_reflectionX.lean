-- Prove2me | solution 1 for MazurTransfer.Order13ReflectionParameter.transcendental_reflectionX
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:10:18.664991+00:00
-- url     : https://prove2.me/submissions/aa752c9b-b7c7-4afd-b54c-35f182358ffb

import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
import Theorems.Thm_MazurTransfer_order13_reflection_coordinate_certificates
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal coefficients for an order-13 reflection, together
with transcendence of its fractional-linear coordinate. Named downstream
consumer: the actual scheme function-field reflection automorphism.
-/

noncomputable section
universe u v
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13ReflectionParameter Polynomial
namespace MazurTransfer.ReflectionParameterTranscendenceProofHelpers20261018
variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

theorem denominator_ne_zero_of_transcendental (t : K) (x : F)
    (hx : Transcendental K x) : reflectionDenominator (algebraMap K F t) x ≠ 0 := by
  intro hz
  by_cases hcoef : algebraMap K F t + 1 = 0
  · simp only [reflectionDenominator, hcoef, zero_mul, zero_add, one_ne_zero] at hz
  · have he : x = -1 / (algebraMap K F t + 1) := by
      apply (eq_div_iff hcoef).mpr
      dsimp [reflectionDenominator] at hz
      linear_combination hz
    apply hx
    rw [he]
    rw [div_eq_mul_inv]
    have ha : IsIntegral K (algebraMap K F t + 1) := isIntegral_algebraMap.add isIntegral_one
    exact ((isIntegral_one (R := K) (B := F)).neg.mul ha.isAlgebraic.inv.isIntegral).isAlgebraic

end MazurTransfer.ReflectionParameterTranscendenceProofHelpers20261018

theorem solution {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (t : K) (x : F)
    (hD : reflectionScalar (algebraMap K F t) ≠ 0)
    (hx : Transcendental K x) : Transcendental K (reflectionX (algebraMap K F t) x) := by
  have hden := MazurTransfer.ReflectionParameterTranscendenceProofHelpers20261018.denominator_ne_zero_of_transcendental t x hx
  intro h
  apply hx
  rw [← (MazurTransfer.order13_reflection_coordinate_certificates.{v}).2.1 (algebraMap K F t) x hD hden]
  change IsAlgebraic K ((algebraMap K F t - reflectionX (algebraMap K F t) x) /
    ((algebraMap K F t + 1) * reflectionX (algebraMap K F t) x + 1))
  rw [div_eq_mul_inv]
  have ht : IsIntegral K (algebraMap K F t) := isIntegral_algebraMap
  exact ((ht.sub h.isIntegral).mul
    (((ht.add isIntegral_one).mul h.isIntegral).add isIntegral_one).isAlgebraic.inv.isIntegral).isAlgebraic

#print axioms solution
