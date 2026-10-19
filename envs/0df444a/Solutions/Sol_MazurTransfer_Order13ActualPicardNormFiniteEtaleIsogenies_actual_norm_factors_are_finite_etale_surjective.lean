-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:20:17.815889+00:00
-- url     : https://prove2.me/submissions/052094ae-5fa6-436b-ac05-bfedf633e46c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual norm endomorphisms of the SAME rational
Picard are finite etale and surjective internal group morphisms. Their
scheme kernels are finite etale over Q. Factor degrees and rank zero
remain separate obligations. Named downstream consumer: actual nineteen
isogeny descent and local/global Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Definitions.Def_MazurTransfer_Order13ActualPicardReducedProperGeometryData
import Definitions.Def_MazurTransfer_Order13ActualPicardConnectedGeometryData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePi_comp_schemePiConjugate
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_comp_schemePi
import Theorems.Thm_MazurTransfer_RelativeGroupSchemeNsmulInternalPowerCompatibility_schemeNsmul_eq_internal_power
import Theorems.Thm_MazurTransfer_SchemeFiniteEtaleEndomorphismSurjectivity_finiteEtaleEndomorphism_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardReducedProperGeometry
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance actualPicardFiniteEtaleNormProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance actualPicardFiniteEtaleNormProvider220261017 : IsReduced actualPicard.P := actualPicard_reduced
local instance actualPicardFiniteEtaleNormProvider320261017 : IsSeparated actualPicard.toBase := actualPicard_separated



local instance actualPicardFiniteEtaleNormProvider420261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance actualPicardFiniteEtaleNormProvider520261017 : Algebra ℚ (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField ℚ) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra ℚ
local instance actualPicardFiniteEtaleNormProvider620261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj



open MazurTransfer.Order13ActualPicardConnectedGeometry
local instance actualPicardFiniteEtaleNormProvider720261017 : Smooth actualPicard.toBase := actualPicard_smooth
local instance actualPicardFiniteEtaleNormProvider820261017 : ConnectedSpace actualPicard.P := actualPicard_connected
local instance actualPicardFiniteEtaleNormProvider920261017 : ConnectedSpace (Over.mk actualPicard.toBase).left := actualPicard_connected
local instance actualPicardFiniteEtaleNormProvider1020261017 : IsLocallyNoetherian actualPicard.P :=
  LocallyOfFiniteType.isLocallyNoetherian actualPicard.toBase
local instance actualPicardFiniteEtaleNormProvider1120261017 : IsLocallyNoetherian (Over.mk actualPicard.toBase).left :=
  LocallyOfFiniteType.isLocallyNoetherian actualPicard.toBase


namespace MazurTransfer.ActualPicardFiniteEtaleNormFactorHelpers20261017
theorem actualLaw_schemeNsmul_eq_internal_power (n : ℕ) :
    actualLaw.schemeNsmul n = ((𝟙 (Over.mk actualPicard.toBase)) ^ n).left :=
  RelativeGroupSchemeNsmulInternalPowerCompatibility.schemeNsmul_eq_internal_power actualPicard.toBase n

theorem actualPicard_schemeNsmul_nineteen_formallyUnramified :
    FormallyUnramified (actualLaw.schemeNsmul 19) :=
  RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing actualLaw
    (show actualLaw.IsCommutative from
      RepresentsRelSubPic.relativeGroupLaw_isCommutative
        (P := algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
        actualRepresentation) 19 (isUnit_iff_ne_zero.mpr (by norm_num))

theorem schemePi_underlying_norm :
    schemePi.left ≫ schemePiConjugate.left = actualLaw.schemeNsmul 19 := by
  rw [actualLaw_schemeNsmul_eq_internal_power]
  exact congrArg (fun f => f.left) schemePi_comp_schemePiConjugate

theorem schemePiConjugate_underlying_norm :
    schemePiConjugate.left ≫ schemePi.left = actualLaw.schemeNsmul 19 := by
  rw [actualLaw_schemeNsmul_eq_internal_power]
  exact congrArg (fun f => f.left) schemePiConjugate_comp_schemePi

theorem schemePi_formallyUnramified : FormallyUnramified schemePi.left := by
  letI : FormallyUnramified (schemePi.left ≫ schemePiConjugate.left) := by
    rw [schemePi_underlying_norm]
    exact actualPicard_schemeNsmul_nineteen_formallyUnramified
  exact FormallyUnramified.of_comp schemePi.left schemePiConjugate.left

theorem schemePiConjugate_formallyUnramified : FormallyUnramified schemePiConjugate.left := by
  letI : FormallyUnramified (schemePiConjugate.left ≫ schemePi.left) := by
    rw [schemePiConjugate_underlying_norm]
    exact actualPicard_schemeNsmul_nineteen_formallyUnramified
  exact FormallyUnramified.of_comp schemePiConjugate.left schemePi.left

theorem actualPicard_over_endomorphism_proper
    (f : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) : IsProper f.left := by
  letI : IsProper (f.left ≫ actualPicard.toBase) := by
    rw [show f.left ≫ actualPicard.toBase = actualPicard.toBase from Over.w f]
    exact actualPicard_proper
  exact IsProper.of_comp f.left actualPicard.toBase

theorem schemePi_locallyQuasiFinite : LocallyQuasiFinite schemePi.left := by
  letI := schemePi_formallyUnramified
  letI := actualPicard_over_endomorphism_proper schemePi
  exact LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType schemePi.left

theorem schemePiConjugate_locallyQuasiFinite : LocallyQuasiFinite schemePiConjugate.left := by
  letI := schemePiConjugate_formallyUnramified
  letI := actualPicard_over_endomorphism_proper schemePiConjugate
  exact LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType schemePiConjugate.left

theorem schemePi_isFinite : IsFinite schemePi.left := by
  letI := actualPicard_over_endomorphism_proper schemePi
  letI := schemePi_locallyQuasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite schemePi.left

theorem schemePiConjugate_isFinite : IsFinite schemePiConjugate.left := by
  letI := actualPicard_over_endomorphism_proper schemePiConjugate
  letI := schemePiConjugate_locallyQuasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite schemePiConjugate.left

theorem schemePi_flat : Flat schemePi.left := by
  letI : LocallyQuasiFinite schemePi.left := schemePi_locallyQuasiFinite
  exact AlgebraicGeometry.flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
    (f := actualPicard.toBase) schemePi.left (Over.w schemePi)

theorem schemePiConjugate_flat : Flat schemePiConjugate.left := by
  letI : LocallyQuasiFinite schemePiConjugate.left := schemePiConjugate_locallyQuasiFinite
  exact AlgebraicGeometry.flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
    (f := actualPicard.toBase) schemePiConjugate.left (Over.w schemePiConjugate)

theorem schemePi_etale : Etale schemePi.left := by
  letI : IsFinite schemePi.left := schemePi_isFinite
  letI : Flat schemePi.left := schemePi_flat
  letI : FormallyUnramified schemePi.left := schemePi_formallyUnramified
  exact Etale.of_formallyUnramified_of_flat schemePi.left

theorem schemePiConjugate_etale : Etale schemePiConjugate.left := by
  letI : IsFinite schemePiConjugate.left := schemePiConjugate_isFinite
  letI : Flat schemePiConjugate.left := schemePiConjugate_flat
  letI : FormallyUnramified schemePiConjugate.left := schemePiConjugate_formallyUnramified
  exact Etale.of_formallyUnramified_of_flat schemePiConjugate.left

theorem schemePi_surjective : Surjective schemePi.left := by
  letI : IsFinite schemePi.left := schemePi_isFinite
  letI : Etale schemePi.left := schemePi_etale
  exact SchemeFiniteEtaleEndomorphismSurjectivity.finiteEtaleEndomorphism_surjective schemePi.left

theorem schemePiConjugate_surjective : Surjective schemePiConjugate.left := by
  letI : IsFinite schemePiConjugate.left := schemePiConjugate_isFinite
  letI : Etale schemePiConjugate.left := schemePiConjugate_etale
  exact SchemeFiniteEtaleEndomorphismSurjectivity.finiteEtaleEndomorphism_surjective schemePiConjugate.left


end MazurTransfer.ActualPicardFiniteEtaleNormFactorHelpers20261017
open MazurTransfer.ActualPicardFiniteEtaleNormFactorHelpers20261017
theorem solution :
    (IsFinite schemePi.left ∧ Etale schemePi.left ∧ Surjective schemePi.left) ∧
    (IsFinite schemePiConjugate.left ∧ Etale schemePiConjugate.left ∧ Surjective schemePiConjugate.left) :=
  ⟨⟨schemePi_isFinite, schemePi_etale, schemePi_surjective⟩,
    ⟨schemePiConjugate_isFinite, schemePiConjugate_etale, schemePiConjugate_surjective⟩⟩


#print axioms solution
