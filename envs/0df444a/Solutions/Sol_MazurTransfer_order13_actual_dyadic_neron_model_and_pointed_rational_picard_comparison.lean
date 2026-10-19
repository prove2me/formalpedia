-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_neron_model_and_pointed_rational_picard_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T09:01:06.510623+00:00
-- url     : https://prove2.me/submissions/32296a68-c8bf-4e3e-9757-5fe936c19357

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original chosen actual dyadic Picard Neron model and its same pointed rational Picard fibre.
Named downstream consumer: extensions and inertia of both actual nineteen norm maps.
-/
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
import Definitions.Def_MazurTransfer_Order13DyadicOriginalChosenRationalPicardComparisonData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedRationalPicardComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedRationalPicardComparison
attribute [local instance] MazurTransfer.Order13DyadicMixedRationalPicardComparison.instFactPrimeOfNatNat_order13DyadicMixedRationalPicardComparison
attribute [local instance] MazurTransfer.Order13DyadicMixedRationalPicardComparison.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard
namespace MazurTransfer.ActualDyadicOriginalNeronRationalPicardProofBoundary20261019
end MazurTransfer.ActualDyadicOriginalNeronRationalPicardProofBoundary20261019
theorem solution : (AbelianSchemePropertyBundle BaseRing dyadicPicard.toBase) ∧ (NeronModelPropertyBundle BaseRing ℚ dyadicPicard.toBase) ∧ (rationalPicard.toBase =
    pullback.snd dyadicPicard.toBase (specGenericFibreInclusion BaseRing ℚ)) ∧ (actualDyadicRationalSchemeIso.hom ≫ rationalPicard.toBase = actualPicard.toBase) ∧ (actualPicard.zeroSection ≫ actualDyadicRationalSchemeIso.hom = rationalPicard.zeroSection) ∧ (@IsMonHom _ _ _ _ _ (@GrpObj.toMonObj _ _ _ _ actualGroup) (@GrpObj.toMonObj _ _ _ _ rationalGroup) actualDyadicRationalOverIso.hom) := by
  exact ⟨MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.dyadicPicard_abelian, MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.dyadicPicard_neron, MazurTransfer.Order13DyadicMixedRationalPicardComparison.rationalPicard_toBase, MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualDyadicRationalSchemeIso_over, MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualDyadicRationalSchemeIso_zero, MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualDyadicRationalOverIso_isMonHom⟩
#print axioms solution
