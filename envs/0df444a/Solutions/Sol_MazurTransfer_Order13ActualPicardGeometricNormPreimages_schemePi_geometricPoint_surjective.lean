-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricNormPreimages.schemePi_geometricPoint_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:38:16.666256+00:00
-- url     : https://prove2.me/submissions/0c922d5d-4482-4b6d-b509-e7befdc91d14

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

namespace MazurTransfer.ActualPiGeometricNormPreimageHelpers20261017
theorem schemePi_isFinite : IsFinite schemePi.left :=
  (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1

theorem schemePi_surjective : Surjective schemePi.left :=
  (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.2.2

end MazurTransfer.ActualPiGeometricNormPreimageHelpers20261017
open MazurTransfer.ActualPiGeometricNormPreimageHelpers20261017
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : Points K) :
    ∃ b : Points K, b ≫ schemePi = a := by
  letI : IsFinite schemePi.left := schemePi_isFinite
  letI : Surjective schemePi.left := schemePi_surjective
  exact IntegralSurjectiveOverGeometricPointLifting.exists_over_comp_eq
    actualPicard.toBase schemePi K _ a


#print axioms solution
