-- Prove2me | solution 1 for MazurTransfer.Order13ActualReflectionCoefficientCovariance.coefficientSemilinearAut_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:49:34.482658+00:00
-- url     : https://prove2.me/submissions/1342e5d5-04e3-4050-b634-84b54a4bb6a3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: coefficient Galois conjugation of the literal reflection
on the SAME actual curve function field. Named downstream consumer: its
geometric curve and Picard comparison, then the actual kernel character.
No identification with the arithmetic Picard action is asserted here.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
noncomputable section
universe u
open MazurTransfer AlgebraicCurve
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open Order13ActualReflectionFunctionField Order13ActualFunctionFieldCoefficientAction
open Order13FieldDiamondFunctionFieldAutomorphism Order13ActualReflectionCoefficientCovariance
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart
attribute [local instance] MazurTransfer.Order13ActualReflectionCoefficientCovariance.reflectionCoefficientOriginalFactProvider20261018
  MazurTransfer.Order13ActualReflectionCoefficientCovariance.reflectionCoefficientOriginalAlgebraProvider20261018
namespace MazurTransfer.ReflectionCoefficientCovarianceProofHelpers20261018
variable (K : Type u) [Field K] [CharZero K]
theorem coefficientFieldMap_reflection (σ : K ≃+* K) (a : ReflectionParameter K) :
    (coefficientFieldMap K σ).comp (reflectionFieldMap K a) =
      (reflectionFieldMap K (mapParameter K σ a)).comp (coefficientFieldMap K σ) := by
  apply fieldMap_ext_xy K
  · intro r
    simp only [RingHom.comp_apply, reflectionFieldMap_algebraMap, coefficientFieldMap_algebraMap]
  · simp only [RingHom.comp_apply, reflectionFieldMap_x, map_reflectionX,
      parameterT, coefficientFieldMap_algebraMap, coefficientFieldMap_x, mapParameter]
  · simp only [RingHom.comp_apply, reflectionFieldMap_y, map_reflectionY,
      parameterT, parameterS, coefficientFieldMap_algebraMap, coefficientFieldMap_x,
      coefficientFieldMap_y, mapParameter]

end MazurTransfer.ReflectionCoefficientCovarianceProofHelpers20261018
open MazurTransfer.ReflectionCoefficientCovarianceProofHelpers20261018
variable (K : Type u) [Field K] [CharZero K]
theorem solution (σ : K ≃+* K) (a : ReflectionParameter K) :
    coefficientSemilinearAut K σ * SemilinearAut.ofAlgAut (reflectionAlgEquiv K a) =
      SemilinearAut.ofAlgAut (reflectionAlgEquiv K (mapParameter K σ a)) * coefficientSemilinearAut K σ := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact RingHom.congr_fun (coefficientFieldMap_reflection K σ a) x
  · apply RingEquiv.ext
    intro x
    rfl

#print axioms solution
