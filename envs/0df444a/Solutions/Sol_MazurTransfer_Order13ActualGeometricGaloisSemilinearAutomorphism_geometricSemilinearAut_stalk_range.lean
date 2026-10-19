-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_stalk_range
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:24:32.967982+00:00
-- url     : https://prove2.me/submissions/6c5ab2ee-51f1-4a6e-8ba6-845af38e69ae

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the original actual geometric semilinear Galois lift
commutes with the literal generic-stalk map and transports stalk ranges.
Named downstream consumer: actual semilinear divisor-presentation transport
and geometric Picard divisor-class Galois compatibility. -/
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
open MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (x : curveScheme K) :
    (SemilinearAut.toRingAut (geometricSemilinearAut K σ)) ''
        ((algebraMap ((curveScheme K).presheaf.stalk ((geometricCurveGaloisIso K σ).hom.base x))
          (actualCurveFunctionField K)).range : Set (actualCurveFunctionField K)) =
      ((algebraMap ((curveScheme K).presheaf.stalk x) (actualCurveFunctionField K)).range :
        Set (actualCurveFunctionField K)) := by
  change MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull.equivOfIso (geometricCurveGaloisIso K σ) '' _ = _
  exact MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull.image_equivOfIso_range_stalk _ x


#print axioms solution
