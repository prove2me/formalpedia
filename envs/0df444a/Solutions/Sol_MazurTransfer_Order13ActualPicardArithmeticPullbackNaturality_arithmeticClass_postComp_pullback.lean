-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardArithmeticPullbackNaturality.arithmeticClass_postComp_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:38:09.205978+00:00
-- url     : https://prove2.me/submissions/4ccc05d7-62cd-4a89-9609-ae07ca9a5b63

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full arithmetic pullback-naturality contract and proof, using accepted
public presentation transport and arithmetic presentation independence.
The original inverse-over-base certificate is supplied by the public field-action
Definition; complete original types and data values were checked separately.
Design boundary: genuine re-rigidified represented Picard pullback induces
the actual field action on the original arithmetic Pic0 class.
Named downstream consumer: diamond Picard scheme action and norm/rank descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
import Theorems.Thm_MazurTransfer_Order13ActualCurveDivisorPresentationPullback_presentation_pullback
import Theorems.Thm_MazurTransfer_PicardCurvePullbackBaseFieldLineBundle_pointLineBundle_postComp_iso_pullback
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
noncomputable section
open MazurTransfer
open Order13ActualPicardArithmeticPullbackNaturality
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open PicardReRigidifiedCurvePullback LineBundleFieldComparison Order13ArithmeticPicardPointMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ


theorem solution
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) (curveToBase ℚ))
    (D : RelativePic0Designation ℚ (curveToBase ℚ))
    (h : RepresentsRelSubPic (curveToBase ℚ) ε (algEquivZeroCut (curveToBase ℚ) ε) D)
    (σ : F ≃ₐ[ℚ] F)
    (N : PullbackData h (fieldLift σ).inv (inverse_over σ))
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) D.toBase) :
    arithmeticClass ℚ 𝒱 ε D h (postComp N.hom a) =
      σ • arithmeticClass ℚ 𝒱 ε D h a := by
  obtain ⟨E, φ, hE⟩ := order13_actual_picard_point_degreeZero_divisor_presentation ℚ 𝒱 ε D h a
  have hEa := arithmeticClass_eq_of_presentation ℚ 𝒱 ε D h a E φ hE
  obtain ⟨ψ, hψ⟩ := Order13ActualCurveDivisorPresentationPullback.presentation_pullback σ
    (pointLineBundle (curveToBase ℚ) ε D h a) E.1 φ hE
  obtain ⟨e⟩ := PicardCurvePullbackBaseFieldLineBundle.pointLineBundle_postComp_iso_pullback
    (curveToBase ℚ) ε D h (fieldLift σ).inv (inverse_over σ) N a
  have htarget := IsPresentation.of_iso e hψ
  have hNb := arithmeticClass_eq_of_presentation ℚ 𝒱 ε D h (postComp N.hom a)
    (Pic0.degZeroSMulHom σ E) _ htarget
  calc
    arithmeticClass ℚ 𝒱 ε D h (postComp N.hom a) = Pic0.mk (Pic0.degZeroSMulHom σ E) := hNb.symm
    _ = σ • Pic0.mk E := (Pic0.smul_mk σ E).symm
    _ = σ • arithmeticClass ℚ 𝒱 ε D h a := congrArg (fun x => σ • x) hEa

#print axioms solution
