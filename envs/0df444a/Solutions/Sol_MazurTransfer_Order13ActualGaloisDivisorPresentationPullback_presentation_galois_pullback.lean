-- Prove2me | solution 1 for MazurTransfer.Order13ActualGaloisDivisorPresentationPullback.presentation_galois_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:46:44.762801+00:00
-- url     : https://prove2.me/submissions/91d647f5-ae48-4b25-8dfd-acf33d02b534

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: pullback along the literal actual curve Galois isomorphism
transports every full divisor presentation to the divisor of the original
geometric semilinear lift. No generic or place-action premise is added.
Named downstream consumer: actual geometric Picard divisor-class Galois naturality. -/
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Theorems.Thm_MazurTransfer_SemilinearCurveIsoDivisorPresentationFieldAction_presentation_pullback
import Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphism_geometricSemilinearAut_generic
import Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisPlaceSet_galois_preimage_placesOf
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
open Order13ActualGeometricGaloisPlaceSet
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (L : (curveScheme K).Modules)
    (D : Divisor K (actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens, Γ(L, U) →+ actualCurveFunctionField K)
    (h : IsPresentation (curveToBase K) L D φ) :
    ∃ ψ : ∀ U : (curveScheme K).Opens,
      Γ((Scheme.Modules.pullback (geometricCurveGaloisIso K σ).hom).obj L, U) →+
        actualCurveFunctionField K,
      IsPresentation (curveToBase K) ((Scheme.Modules.pullback (geometricCurveGaloisIso K σ).hom).obj L)
        (geometricSemilinearAut K σ • D) ψ :=
  SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback (curveToBase K)
    (geometricCurveGaloisIso K σ).symm (geometricSemilinearAut K σ) L D φ h
    (geometricSemilinearAut_generic K σ).symm (galois_preimage_placesOf K σ)

#print axioms solution
