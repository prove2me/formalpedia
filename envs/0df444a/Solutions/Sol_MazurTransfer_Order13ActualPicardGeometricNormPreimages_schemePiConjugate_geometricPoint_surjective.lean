-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricNormPreimages.schemePiConjugate_geometricPoint_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:38:49.335079+00:00
-- url     : https://prove2.me/submissions/b35fd5b5-8120-4449-95eb-0f3e8e964770

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both finite etale norm endomorphisms of the SAME
rational represented Picard have preimages on algebraically closed
field points. Named downstream consumer: actual norm Kummer cocycles.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricFieldPointsData
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
import Theorems.Thm_MazurTransfer_IntegralSurjectiveOverGeometricPointLifting_exists_over_comp_eq
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open MazurTransfer.Order13ActualPicardGeometricNormPreimages

namespace MazurTransfer.ActualPiConjugateGeometricNormPreimageHelpers20261017
theorem schemePiConjugate_isFinite : IsFinite schemePiConjugate.left :=
  (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1

theorem schemePiConjugate_surjective : Surjective schemePiConjugate.left :=
  (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.2.2

end MazurTransfer.ActualPiConjugateGeometricNormPreimageHelpers20261017
open MazurTransfer.ActualPiConjugateGeometricNormPreimageHelpers20261017
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : Points K) :
    ∃ b : Points K, b ≫ schemePiConjugate = a := by
  letI : IsFinite schemePiConjugate.left := schemePiConjugate_isFinite
  letI : Surjective schemePiConjugate.left := schemePiConjugate_surjective
  exact IntegralSurjectiveOverGeometricPointLifting.exists_over_comp_eq
    actualPicard.toBase schemePiConjugate K _ a


#print axioms solution
