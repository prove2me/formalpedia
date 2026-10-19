-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_generic
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:21:44.121548+00:00
-- url     : https://prove2.me/submissions/a75011cb-bdf3-48db-bcd8-5a9b1fed3d05

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the original actual geometric semilinear Galois lift
commutes with the literal generic-stalk map and transports stalk ranges.
Named downstream consumer: actual semilinear divisor-presentation transport
and geometric Picard divisor-class Galois compatibility. -/
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
import Theorems.Thm_MazurTransfer_CurveIsoGenericFieldDiagram_equivOfIso_spec
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
open MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) :
    Spec.map (CommRingCat.ofHom (SemilinearAut.toRingAut (geometricSemilinearAut K σ)).toRingHom) ≫
        (curveScheme K).fromSpecStalk (genericPoint (curveScheme K)) =
      (curveScheme K).fromSpecStalk (genericPoint (curveScheme K)) ≫
        (geometricCurveGaloisIso K σ).hom := by
  change Spec.map (CommRingCat.ofHom (MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull.equivOfIso (geometricCurveGaloisIso K σ)).toRingHom) ≫
    (curveScheme K).fromSpecStalk (genericPoint (curveScheme K)) = _
  exact MazurTransfer.CurveIsoGenericFieldDiagram.equivOfIso_spec _


#print axioms solution
