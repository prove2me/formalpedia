-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricGaloisCoefficientComparison.geometricSemilinearAut_eq_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:52:26.701107+00:00
-- url     : https://prove2.me/submissions/9479bdf7-d04f-4bb4-a4d1-a8099cca16d7

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the geometric semilinear lift associated to the SAME actual
curve Galois isomorphism equals its coordinate-defined coefficient lift.
Named downstream consumer: arithmetic Galois covariance of the actual Picard
reflection, and the character of the cyclotomic quotient kernel.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13GeometricGenericEmbeddingBaseChangeData
import Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphism_geometricSemilinearAut_generic
noncomputable section
namespace MazurTransfer.GeometricGaloisCoefficientComparisonProofHelpers20261018
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricGaloisSemilinearAutomorphism
open Order13ActualGeometricCurveGaloisAutomorphism
open Order13ActualFunctionFieldCoefficientAction
open Order13GeometricFunctionFieldBaseChange Order13GeometricGenericEmbeddingBaseChange
open Order13FieldCurveAutomorphismLift Order13ActualCurveBaseChange
open Order13PellActualOrdinaryChart
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
local instance geometricCoefficientOriginalFieldFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance geometricCoefficientOriginalRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance geometricCoefficientOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem geometricSemilinearAut_fieldBaseChange (σ : K ≃ₐ[ℚ] K) :
    (SemilinearAut.toRingAut (geometricSemilinearAut K σ)).toRingHom.comp (fieldBaseChange K) =
      fieldBaseChange K := by
  have : Mono (genericEmbedding ℚ) := by
    change Mono ((curveScheme ℚ).fromSpecStalk (genericPoint (curveScheme ℚ)))
    infer_instance
  have hg : Spec.map (CommRingCat.ofHom (SemilinearAut.toRingAut (geometricSemilinearAut K σ)).toRingHom) ≫
      genericEmbedding K = genericEmbedding K ≫ (geometricCurveGaloisIso K σ).hom :=
    geometricSemilinearAut_generic K σ
  have h : Spec.map (CommRingCat.ofHom (fieldBaseChange K) ≫
      CommRingCat.ofHom (SemilinearAut.toRingAut (geometricSemilinearAut K σ)).toRingHom) ≫
        genericEmbedding ℚ = Spec.map (CommRingCat.ofHom (fieldBaseChange K)) ≫ genericEmbedding ℚ := by
    rw [Spec.map_comp, Category.assoc, ← genericEmbedding_baseChange,
      ← Category.assoc, hg, Category.assoc,
      geometricCurveGaloisIso_curveMap, genericEmbedding_baseChange]
  have he := Spec.map_injective ((cancel_mono (genericEmbedding ℚ)).mp h)
  apply RingHom.ext
  intro b
  exact congrArg (fun f : CommRingCat.of (actualCurveFunctionField ℚ) ⟶
    CommRingCat.of (actualCurveFunctionField K) => f.hom b) he

theorem geometricSemilinearAut_x (σ : K ≃ₐ[ℚ] K) :
    SemilinearAut.toRingAut (geometricSemilinearAut K σ) (xImage K) = xImage K := by
  have h := RingHom.congr_fun (geometricSemilinearAut_fieldBaseChange K σ) (xImage ℚ)
  change SemilinearAut.toRingAut (geometricSemilinearAut K σ) (fieldBaseChange K (xImage ℚ)) =
    fieldBaseChange K (xImage ℚ) at h
  rw [fieldBaseChange_x] at h
  exact h

theorem geometricSemilinearAut_y (σ : K ≃ₐ[ℚ] K) :
    SemilinearAut.toRingAut (geometricSemilinearAut K σ) (yImage K) = yImage K := by
  have h := RingHom.congr_fun (geometricSemilinearAut_fieldBaseChange K σ) (yImage ℚ)
  change SemilinearAut.toRingAut (geometricSemilinearAut K σ) (fieldBaseChange K (yImage ℚ)) =
    fieldBaseChange K (yImage ℚ) at h
  rw [fieldBaseChange_y] at h
  exact h

theorem geometricSemilinearAut_fieldMap_eq (σ : K ≃ₐ[ℚ] K) :
    (SemilinearAut.toRingAut (geometricSemilinearAut K σ)).toRingHom =
      coefficientFieldMap K σ.toRingEquiv := by
  apply coefficientFieldMap_unique K σ.toRingEquiv
  · intro r
    exact SemilinearAut.commutes (geometricSemilinearAut K σ) r
  · exact geometricSemilinearAut_x K σ
  · exact geometricSemilinearAut_y K σ

end MazurTransfer.GeometricGaloisCoefficientComparisonProofHelpers20261018
open MazurTransfer.GeometricGaloisCoefficientComparisonProofHelpers20261018
open AlgebraicCurve MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism
open MazurTransfer.Order13ActualFunctionFieldCoefficientAction
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem solution (σ : K ≃ₐ[ℚ] K) :
    geometricSemilinearAut K σ = coefficientSemilinearAut K σ.toRingEquiv := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact RingHom.congr_fun (geometricSemilinearAut_fieldMap_eq K σ) x
  · rfl

#print axioms solution
