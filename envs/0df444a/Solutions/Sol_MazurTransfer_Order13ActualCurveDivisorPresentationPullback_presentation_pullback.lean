-- Prove2me | solution 1 for MazurTransfer.Order13ActualCurveDivisorPresentationPullback.presentation_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:05:40.841376+00:00
-- url     : https://prove2.me/submissions/95bb94f7-946f-47b3-b0cf-2659e2ac4f02

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve pullback on the literal curve over Q takes
any full divisor presentation to the divisor transported by the specified
actual field automorphism. Named downstream consumer: identification of
the genuine represented Picard action with arithmetic Pic0 transport.
-/
import Theorems.Thm_MazurTransfer_CurveIsoDivisorPresentationFieldAction_presentation_pullback
import Theorems.Thm_MazurTransfer_Order13ActualCurveInversePlaceSet_inverse_placesOf
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualCurveInversePlaceSet
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem solution (σ : F ≃ₐ[ℚ] F) (L : C.Modules) (D : Divisor ℚ F)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ F) (h : IsPresentation (curveToBase ℚ) L D φ) :
    ∃ ψ : ∀ U : C.Opens, Γ((Scheme.Modules.pullback (fieldLift σ).inv).obj L, U) →+ F,
      IsPresentation (curveToBase ℚ) ((Scheme.Modules.pullback (fieldLift σ).inv).obj L)
        (σ • D) ψ :=
  CurveIsoDivisorPresentationFieldAction.presentation_pullback
    (curveToBase ℚ) (fieldLift σ) σ L D φ h
    (fieldLift_inv_generic σ) (inverse_placesOf σ)

#print axioms solution
