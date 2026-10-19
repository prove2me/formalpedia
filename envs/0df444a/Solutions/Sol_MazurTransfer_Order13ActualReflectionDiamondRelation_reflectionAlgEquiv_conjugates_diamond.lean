-- Prove2me | solution 1 for MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_conjugates_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:23:38.19308+00:00
-- url     : https://prove2.me/submissions/28dfff72-a5bb-41be-91a8-4ee2cac67c49

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: composition of the literal function-field reflection and
diamond is the next literal reflection in its coefficient orbit.
Named downstream consumer: the actual Picard reflection that exchanges the
two nineteen-norm kernels, and its arithmetic Galois character.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
noncomputable section
universe u
namespace MazurTransfer.ReflectionDiamondConjugationProofHelpers20261018
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open Order13ReflectionParameterArithmetic Order13DiamondSexticSymmetry

section Coordinates
variable {F : Type u} [Field F]

theorem reflectionX_add_one (t x : F) (hx : reflectionDenominator t x ≠ 0) :
    reflectionX t x + 1 = (t * x + t + 1) / reflectionDenominator t x := by
  apply (eq_div_iff hx).mpr
  dsimp [reflectionX]
  rw [add_mul, div_mul_cancel₀ _ hx]
  dsimp [reflectionDenominator]
  ring

theorem next_denominator (t x : F) (ht : t + 1 ≠ 0) :
    reflectionDenominator (diamondX t) x = (t * x + t + 1) / (t + 1) := by
  apply (eq_div_iff ht).mpr
  dsimp [reflectionDenominator, diamondX]
  field_simp [ht]
  ring

theorem reflection_diamond_x (t x : F) (ht : t + 1 ≠ 0)
    (hx : reflectionDenominator t x ≠ 0) :
    diamondX (reflectionX t x) = reflectionX (diamondX t) x := by
  have hn : diamondX t - x = -reflectionDenominator t x / (t + 1) := by
    apply (eq_div_iff ht).mpr
    dsimp [diamondX]
    rw [sub_mul, div_mul_cancel₀ _ ht]
    dsimp [reflectionDenominator]
    ring
  change -1 / (reflectionX t x + 1) =
    (diamondX t - x) / reflectionDenominator (diamondX t) x
  rw [reflectionX_add_one t x hx, hn, next_denominator t x ht,
    div_div_div_cancel_right₀ ht, div_div_eq_mul_div]
  ring

theorem reflection_diamond_y (t s x y : F) (ht : t + 1 ≠ 0)
    (hx : reflectionDenominator t x ≠ 0) :
    diamondY (reflectionX t x) (reflectionY t s x y) =
      reflectionY (diamondX t) (s / (t + 1)) x y := by
  change (s ^ 3 * y / reflectionDenominator t x ^ 3) / (reflectionX t x + 1) ^ 3 =
    (s / (t + 1)) ^ 3 * y / reflectionDenominator (diamondX t) x ^ 3
  rw [reflectionX_add_one t x hx, next_denominator t x ht, div_pow, div_pow,
    div_div_div_cancel_right₀ (pow_ne_zero 3 hx), div_pow, div_mul_eq_mul_div,
    div_div_div_cancel_right₀ (pow_ne_zero 3 ht)]

end Coordinates

open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ActualReflectionFunctionField
open Order13FieldDiamondFunctionFieldMap Order13FieldDiamondFunctionFieldAutomorphism
variable (K : Type u) [Field K] [CharZero K]
local instance reflectionDiamondOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance reflectionDiamondOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem reflectionFieldMap_diamond (a : ReflectionParameter K) :
    (reflectionFieldMap K a).comp (diamondFieldMap K) =
      reflectionFieldMap K (diamondParameter a) := by
  have ht : parameterT K a + 1 ≠ 0 := by
    have h : algebraMap K (actualCurveFunctionField K) (a.t + 1) ≠ 0 :=
      (_root_.map_ne_zero _).mpr (parameter_t_add_one_ne_zero a)
    simpa only [map_add, map_one] using h
  have hn : parameterT K (diamondParameter a) = diamondX (parameterT K a) := by
    simp only [parameterT, diamondParameter, diamondX, map_div₀, map_neg, map_one, map_add]
  have hs : parameterS K (diamondParameter a) = parameterS K a / (parameterT K a + 1) := by
    simp only [parameterS, parameterT, diamondParameter, map_div₀, map_add, map_one]
  apply fieldMap_ext_xy K
  · intro r
    simp only [RingHom.comp_apply, diamondFieldMap_algebraMap, reflectionFieldMap_algebraMap]
  · simp only [RingHom.comp_apply, diamondFieldMap_x, map_diamondX, reflectionFieldMap_x, hn]
    exact reflection_diamond_x _ _ ht (reflection_denominator_ne_zero K a)
  · simp only [RingHom.comp_apply, diamondFieldMap_y, map_diamondY, reflectionFieldMap_y,
      reflectionFieldMap_x, hn, hs]
    exact reflection_diamond_y _ _ _ _ ht (reflection_denominator_ne_zero K a)

theorem reflectionAlgEquiv_diamond (a : ReflectionParameter K) :
    reflectionAlgEquiv K a * diamondAlgEquiv K = reflectionAlgEquiv K (diamondParameter a) := by
  ext z
  exact RingHom.congr_fun (reflectionFieldMap_diamond K a) z

theorem reflectionAlgEquiv_square (a : ReflectionParameter K) :
    reflectionAlgEquiv K a * reflectionAlgEquiv K a = 1 := by
  ext z
  exact RingHom.congr_fun (reflectionFieldMap_square K a) z

end MazurTransfer.ReflectionDiamondConjugationProofHelpers20261018

open MazurTransfer.ReflectionDiamondConjugationProofHelpers20261018
open MazurTransfer.Order13ReflectionParameterArithmetic
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ReflectionParameter MazurTransfer.Order13ActualReflectionFunctionField
open MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism
variable (K : Type u) [Field K] [CharZero K]
theorem solution (a : ReflectionParameter K) :
    reflectionAlgEquiv K a * diamondAlgEquiv K * reflectionAlgEquiv K a = (diamondAlgEquiv K)⁻¹ := by
  have h : (reflectionAlgEquiv K a * diamondAlgEquiv K) *
      (reflectionAlgEquiv K a * diamondAlgEquiv K) = 1 := by
    rw [reflectionAlgEquiv_diamond K a, reflectionAlgEquiv_square K (diamondParameter a)]
  apply mul_right_cancel (b := diamondAlgEquiv K)
  simpa only [mul_assoc, inv_mul_cancel] using h

#print axioms solution
