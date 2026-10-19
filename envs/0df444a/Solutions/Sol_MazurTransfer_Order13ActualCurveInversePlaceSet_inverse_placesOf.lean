-- Prove2me | solution 1 for MazurTransfer.Order13ActualCurveInversePlaceSet.inverse_placesOf
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:43:40.892197+00:00
-- url     : https://prove2.me/submissions/b4033e6e-864d-46fa-bcff-fa95e01567f6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve preimages of opens transport the literal
sets of closed-point valuation places by the field automorphism. Named
downstream consumer: the range condition for transformed divisor presentations.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondGenericCurveOrder
import Definitions.Def_MazurTransfer_Order13ActualDiamondCurveAutomorphism
import Definitions.Def_AlgebraicCurve_PlacesOf
noncomputable section
open MazurTransfer
namespace MazurTransfer.ActualCurveInversePlaceSetHelpers20261017
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualDiamondCurveAutomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem mem_placesOf_actual_iff (U : C.Opens) (v : Place ℚ F) :
    v ∈ placesOf (curveToBase ℚ) U ↔
      ∃ x : closedPoints C, x.1 ∈ U ∧ actualPlaceOfPoint ℚ x = v := by
  constructor
  · rintro ⟨x, hxU, hx, hv⟩
    refine ⟨⟨x, hx⟩, hxU, ?_⟩
    have hR : (actualPlaceOfPoint ℚ ⟨x, hx⟩).toValuationSubring.toSubring =
        v.toValuationSubring.toSubring := (actualPlaceOfPoint_stalk_range ℚ ⟨x, hx⟩).symm.trans hv
    apply Place.ext
    ext a
    exact Iff.of_eq (congrArg (fun R : Subring F => a ∈ R) hR)
  · rintro ⟨x, hxU, rfl⟩
    exact ⟨x.1, hxU, x.2, actualPlaceOfPoint_stalk_range ℚ x⟩


end MazurTransfer.ActualCurveInversePlaceSetHelpers20261017
open MazurTransfer.ActualCurveInversePlaceSetHelpers20261017
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualDiamondCurveAutomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem solution (σ : F ≃ₐ[ℚ] F) (U : C.Opens) :
    placesOf (curveToBase ℚ) ((fieldLift σ).inv ⁻¹ᵁ U) =
      (fun v : Place ℚ F => σ • v) '' placesOf (curveToBase ℚ) U := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (mem_placesOf_actual_iff _ _).mp hv
    let y := closedPointImage (fieldLift σ).symm x
    have hy : actualPlaceOfPoint ℚ y = σ⁻¹ • actualPlaceOfPoint ℚ x := by
      have h := fieldLift_place σ⁻¹ x
      rw [fieldLift_inv] at h
      exact h
    refine ⟨actualPlaceOfPoint ℚ y, (mem_placesOf_actual_iff U _).mpr ⟨y, hx, rfl⟩, ?_⟩
    change σ • actualPlaceOfPoint ℚ y = actualPlaceOfPoint ℚ x
    rw [hy, smul_inv_smul]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_placesOf_actual_iff U w).mp hw
    let x := closedPointImage (fieldLift σ) y
    apply (mem_placesOf_actual_iff _ _).mpr
    refine ⟨x, ?_, fieldLift_place σ y⟩
    change (fieldLift σ).inv ((fieldLift σ).hom y.1) ∈ U
    have h : (fieldLift σ).inv ((fieldLift σ).hom y.1) = y.1 := by
      exact congrArg (fun f : C ⟶ C => f y.1) (fieldLift σ).hom_inv_id
    rw [h]
    exact hy

#print axioms solution
