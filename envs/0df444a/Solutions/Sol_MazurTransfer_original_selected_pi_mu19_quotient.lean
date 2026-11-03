-- Prove2me | solution 1 for MazurTransfer.original_selected_pi_mu19_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-11-02T16:32:00.112618+00:00
-- url     : https://prove2.me/submissions/99c2fd51-a923-4384-b86a-7ae558c0b245

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the same selected pi quotient, its same finite-flat Hopf model, inclusion and arithmetic label under normalized literal mu19 scalar change.
Named downstream consumer: pushforward of the actual integral pi norm-preimage torsor and its literal mu19 Kummer unit condition.
-/
import Definitions.Def_MazurTransfer_OriginalSelectedPiMu19QuotientData20261020
import Theorems.Thm_MazurTransfer_original_rational_subring_mu19_classification
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SameIntegralPicardRationalSchemeComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13IntegralRepresentationQuotient Order13ActualOrderedCharacterContinuousH1
open Order13RationalSubringBaseChange NineteenRootsGaloisRepresentation
open Order13RationalSubringMu19Classification CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open BialgebraBaseChangePointRestriction
open scoped CategoryTheory.MonObj TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
open MazurTransfer.Order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsMonHomOverSchemeSpecOfRatSchemePi_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instFactPrimeOfNatNat_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsFiniteLeftSchemeSchemePi_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsGaloisRatAlgebraicClosure_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instFactForallEqSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePiHPowOfNat_order13SelectedPiMu19Quotient
attribute [local instance] MazurTransfer.Order13SelectedPiMu19Quotient.instModuleZModOfNatNatAdditiveSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePi_order13SelectedPiMu19Quotient
namespace MazurTransfer.OriginalSelectedPiMu19QuotientBoundary20261020
end MazurTransfer.OriginalSelectedPiMu19QuotientBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the SAME selected piQuotient model in NORMALIZED literal mu19 coordinates, bialgebra
inclusion, arithmetic label and restriction identity when classifying
its canonical scalar base change at nineteen. No replacement quotient.
Named downstream consumer: pushforward of the actual integral pi torsor
and its literal-mu19 Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.OriginalSelectedPiMu19QuotientProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SameIntegralPicardRationalSchemeComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13IntegralRepresentationQuotient Order13ActualOrderedCharacterContinuousH1
open Order13RationalSubringBaseChange NineteenRootsGaloisRepresentation
open Order13RationalSubringMu19Classification CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open BialgebraBaseChangePointRestriction
open scoped CategoryTheory.MonObj TensorProduct













variable (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
variable (G : Type) [CommRing G] [HopfAlgebra R G]
variable (e : WithConv (G →ₐ[R] F) ≃ Additive (Kernel F schemePi))

theorem fixed_base_restriction_square {H : Type} [CommRing H] [HopfAlgebra R H]
    (j : H →ₐc[R] G) (f : WithConv (S ⊗[R] G →ₐ[S] F)) :
    fixedBasePoint H (BialgebraPointRestriction.restrictPoint (baseChangeMap («S» := S) j) f) =
      BialgebraPointRestriction.restrictPoint j (fixedBasePoint G f) := rfl



theorem selected_pi_quotient_retains_normalized_mu19_same_model
    (hQ : HasQuotientOfModel 19 F schemePi (rootsRepresentation F)
      (piQuotient F z hz 𝒱) G e) :
    HasSelectedNormalizedMu19Quotient z hz 𝒱 G e := by
  obtain ⟨H, iCR, iHA, hFin, hFlat, hComm, j, e', hInj, hAdd, hAct, hRestr⟩ := hQ
  letI := iCR
  letI := iHA
  letI := hFin
  letI := hFlat
  letI := hComm
  letI hFree : Module.Free R H := Module.free_of_flat_of_isLocalRing
  obtain ⟨ψ, hψ⟩ := MazurTransfer.original_rational_subring_mu19_classification H e' hAdd hAct
  refine ⟨H, iCR, iHA, hFin, hFree, hComm, hFlat, j, e', hInj, hAdd, hAct, hRestr, ψ, hψ, ?_⟩
  intro f
  change literalPointEquiv ψ F (BialgebraPointRestriction.restrictPoint
    (baseChangeMap («S» := S) j) f) = _
  rw [hψ, fixed_base_restriction_square, hRestr]

end MazurTransfer.OriginalSelectedPiMu19QuotientProof20261020

theorem solution : (∀ (G : Type) [CommRing G] [HopfAlgebra R G], ∀ {H : Type} [CommRing H] [HopfAlgebra R H]
    (j : H →ₐc[R] G) (f : WithConv (S ⊗[R] G →ₐ[S] F)),
fixedBasePoint H (BialgebraPointRestriction.restrictPoint (baseChangeMap («S» := S) j) f) =
      BialgebraPointRestriction.restrictPoint j (fixedBasePoint G f)) ∧ (∀ (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (G : Type) [CommRing G] [HopfAlgebra R G] (e : WithConv (G →ₐ[R] F) ≃ Additive (Kernel F schemePi)), ∀ (hQ : HasQuotientOfModel 19 F schemePi (rootsRepresentation F)
      (piQuotient F z hz 𝒱) G e),
HasSelectedNormalizedMu19Quotient z hz 𝒱 G e) := by
  exact ⟨MazurTransfer.OriginalSelectedPiMu19QuotientProof20261020.fixed_base_restriction_square, MazurTransfer.OriginalSelectedPiMu19QuotientProof20261020.selected_pi_quotient_retains_normalized_mu19_same_model⟩
#print axioms solution
