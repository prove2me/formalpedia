-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricGaloisPlaceSet.galois_preimage_placesOf
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:26:58.920205+00:00
-- url     : https://prove2.me/submissions/5b379d1c-95ce-4b1f-bf43-fb4eeef941ee

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the actual geometric semilinear Galois lift carries
closed-point valuation places in an open to those in its Galois preimage.
Named downstream consumer: actual semilinear divisor-presentation transport
and geometric Picard divisor-class Galois compatibility. -/
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
import Definitions.Def_MazurTransfer_Order13FieldCurveInversePlaceSetData
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
open Order13FieldCurveInversePlaceSet CurveClosedPointImage
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018
namespace MazurTransfer.ActualGeometricGaloisPlaceTransportProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem geometricSemilinearAut_stalk_range (σ : K ≃ₐ[ℚ] K) (x : curveScheme K) :
    (SemilinearAut.toRingAut (geometricSemilinearAut K σ)) ''
        ((algebraMap ((curveScheme K).presheaf.stalk ((geometricCurveGaloisIso K σ).hom.base x))
          (actualCurveFunctionField K)).range : Set (actualCurveFunctionField K)) =
      ((algebraMap ((curveScheme K).presheaf.stalk x) (actualCurveFunctionField K)).range :
        Set (actualCurveFunctionField K)) := by
  change MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull.equivOfIso (geometricCurveGaloisIso K σ) '' _ = _
  exact MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull.image_equivOfIso_range_stalk _ x


theorem actualPlace_coe_stalk_range (x : closedPoints (curveScheme K)) :
    ((actualPlaceOfPoint K x).toValuationSubring : Set (actualCurveFunctionField K)) =
      ((algebraMap ((curveScheme K).presheaf.stalk x.val) (actualCurveFunctionField K)).range :
        Set (actualCurveFunctionField K)) :=
  congrArg (fun S : Subring (actualCurveFunctionField K) => (S : Set (actualCurveFunctionField K)))
    (actualPlaceOfPoint_stalk_range K x).symm


theorem actualPlace_geometric_galois (σ : K ≃ₐ[ℚ] K) (x : closedPoints (curveScheme K)) :
    geometricSemilinearAut K σ • actualPlaceOfPoint K (closedPointImage (geometricCurveGaloisIso K σ) x) =
      actualPlaceOfPoint K x := by
  apply Place.ext
  apply SetLike.coe_injective
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.coe_pointwise_smul, ← Set.image_smul]
  change (SemilinearAut.toRingAut (geometricSemilinearAut K σ)) ''
    ((actualPlaceOfPoint K (closedPointImage (geometricCurveGaloisIso K σ) x)).toValuationSubring : Set _) = _
  rw [actualPlace_coe_stalk_range, actualPlace_coe_stalk_range]
  exact geometricSemilinearAut_stalk_range K σ x.val


end MazurTransfer.ActualGeometricGaloisPlaceTransportProofHelpers20261018
open MazurTransfer.ActualGeometricGaloisPlaceTransportProofHelpers20261018
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (U : (curveScheme K).Opens) :
    placesOf (curveToBase K) ((geometricCurveGaloisIso K σ).hom ⁻¹ᵁ U) =
      (fun v : Place K (actualCurveFunctionField K) => geometricSemilinearAut K σ • v) ''
        placesOf (curveToBase K) U := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (mem_placesOf_actual_iff K _ _).mp hv
    let y := closedPointImage (geometricCurveGaloisIso K σ) x
    exact ⟨actualPlaceOfPoint K y, (mem_placesOf_actual_iff K U _).mpr ⟨y, hx, rfl⟩,
      actualPlace_geometric_galois K σ x⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_placesOf_actual_iff K U w).mp hw
    let x := closedPointImage (geometricCurveGaloisIso K σ).symm y
    have hxy : closedPointImage (geometricCurveGaloisIso K σ) x = y := by
      apply Subtype.ext
      exact congrArg (fun f : curveScheme K ⟶ curveScheme K => f y.val)
        (geometricCurveGaloisIso K σ).inv_hom_id
    apply (mem_placesOf_actual_iff K _ _).mpr
    refine ⟨x, ?_, ?_⟩
    · change (geometricCurveGaloisIso K σ).hom x.val ∈ U
      have hval : (geometricCurveGaloisIso K σ).hom x.val = y.val := congrArg Subtype.val hxy
      rw [hval]
      exact hy
    · have h := actualPlace_geometric_galois K σ x
      rw [hxy] at h
      exact h.symm


#print axioms solution
