-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ac585c06-09e4-56f7-9351-8b675bcd9ae0

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_DRModelPackageLevel_crossingPt_mem_preimage_iotaFin
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
import Theorems.Thm_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
p2m_attr_erase "instance" "ModularCurve.eisensteinMaximalIdeal.isPrime ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instCommRing_H ModularCurve.JZeroNeronPrimaryTorsionCore.instHopfAlgebra_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_Hff ModularCurve.JZeroNeronPrimaryTorsionCore.instFlat_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instFiniteType_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFlat_Hff ModularCurve.JZeroNeronDataPrime.instFiniteΦ ModularCurve.JZeroNeronDataPrime.instAddCommGroupΦ ModularCurve.JZeroNeronDataPrime.instModuleΦ ModularCurve.JZeroNeronData.instAddCommGroupΦ ModularCurve.JZeroNeronData.instModuleΦ ModularCurve.JZeroNeronData.instFiniteΦ AlgebraicGeometry.Scheme.Fppf.instLocallyOfFinitePresentationHomDiscretePUnit AlgebraicGeometry.Scheme.Fppf.instFlatHomDiscretePUnit AlgebraicGeometry.Scheme.instAdditiveAbFunctorOppositeFppfConst AlgebraicGeometry.Scheme.instHasIsosFppfPrecoverage_definitions AlgebraicGeometry.Scheme.Fppf.instFullOverForget AlgebraicGeometry.Scheme.instAdditiveAbSheafFppfSmallFppfTopologyConstantSheaf AlgebraicGeometry.Scheme.hasSheafify_smallFppfTopology AlgebraicGeometry.Scheme.instCategoryFppf AlgebraicGeometry.Scheme.instIsCocontinuousFppfOverForgetSmallFppfTopologyOverFppfTopology AlgebraicGeometry.Scheme.instHasTerminalFppf AlgebraicGeometry.Scheme.instIsMultiplicativeLocallyOfFinitePresentation_definitions AlgebraicGeometry.Scheme.abelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.hasExt_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.instLocallyCoverDenseFppfOverForgetOverFppfTopology AlgebraicGeometry.Scheme.Fppf.instFaithfulOverForget AlgebraicGeometry.Scheme.instAddCommGroupFppfCohomology AlgebraicGeometry.Scheme.instHasPullbacksFppfPrecoverage_definitions FppfCohomologyLES.fppfSheavesIsGrothendieckAbelian ModularCurve.AdmissibleInvariants.instAdd"
p2m_attr_erase "instance" "ModularCurve.AdmissibleInvariants.instZero FppfRepresentableGroupSchemeSheaf.instIsCommMonObjSchemeTensorUnit_definitions FppfRepresentableGroupSchemeSheaf.gateTrivialSheafSectionsSubsingleton ValuationSubring.instIsAlgClosedResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.JZeroNeronObjectAtP.LevelData.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.mk.injEq ModularCurve.JZeroNeronObjectAtP.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.LevelData.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.injEq ModularCurve.JZeroNeronDataPrime.mk.sizeOf_spec ModularCurve.JZeroNeronDataPrime.mk.injEq ModularCurve.JZeroNeronData.mk.injEq ModularCurve.JZeroNeronData.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.eisensteinEval_heckeGen ModularCurve.modSystem_apply ModularCurve.FppfKummerData.mk.injEq ModularCurve.JKummerRow.mk.injEq ModularCurve.JKummerRow.mk.sizeOf_spec ModularCurve.FppfKummerData.mk.sizeOf_spec ModularCurve.coe_cuspidalDivisor₀ FppfCohomologyLES.cohomologyMapAddEquiv_apply FppfCohomologyLES.biprodSESHom_τ₃ FppfCohomologyLES.cohomologyMap_apply FppfCohomologyLES.cohomologyδ_apply FppfCohomologyLES.cohomologyMapAddEquiv_symm_apply FppfCohomologyLES.biprodSESHom_τ₁ ModularCurve.AdmissibleInvariants.zero_h1 ModularCurve.AdmissibleInvariants.add_h0 ModularCurve.AdmissibleInvariants.zero_δ ModularCurve.AdmissibleInvariants.zero_α ModularCurve.AdmissibleInvariants.zero_h0 ModularCurve.AdmissibleInvariants.add_α"
p2m_attr_erase "simp" "ModularCurve.AdmissibleInvariants.mk.sizeOf_spec FppfKummerSES.kummerSES_g FppfKummerSES.kummerSES_X₃ ModularCurve.AdmissibleInvariants.genericDefect_zero ModularCurve.AdmissibleInvariants.add_δ ModularCurve.AdmissibleInvariants.add_h1 FppfKummerSES.kummerSES_X₁ ModularCurve.AdmissibleInvariants.mk.injEq ModularCurve.AdmissibleInvariants.eulerDefect_zero FppfKummerSES.kummerSES_X₂ GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open scoped TensorProduct

noncomputable section

namespace OggTLevel

theorem comp_base_apply' {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

namespace RingStalk

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra (DRLevel.R ℓ) O]

private abbrev _root_.OggTLevel.RingStalk.XO : Scheme.{0} := pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O)))

p2m_export "OggTLevel.RingStalk" "XO"

abbrev PFin := pullback (IgusaScheme.ιFin N ℓ) (pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O))))

abbrev gFin : PFin N ℓ O ⟶ XO N ℓ O := pullback.snd _ _

def isoFin : PFin N ℓ O ≅ Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) :=
  pullbackRightPullbackFstIso (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O))) (IgusaScheme.ιFin N ℓ) ≪≫
    pullback.congrHom (IgusaScheme.ιFin_igusaTo N ℓ) rfl ≪≫ pullbackSpecIso (DRLevel.R ℓ) ↥(IgusaScheme.chartAlgFin N ℓ) O

def chartFin : Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) ⟶ XO N ℓ O :=
  (isoFin N ℓ O).inv ≫ gFin N ℓ O

scoped instance : IsOpenImmersion (chartFin N ℓ O) := by
  unfold chartFin; infer_instance

theorem chartFin_fst : chartFin N ℓ O ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R ℓ) (A := ↥(IgusaScheme.chartAlgFin N ℓ)) (B := O))) ≫
      IgusaScheme.ιFin N ℓ := by
  have hc : gFin N ℓ O ≫ pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O))) =
      pullback.fst (IgusaScheme.ιFin N ℓ) _ ≫ IgusaScheme.ιFin N ℓ := pullback.condition.symm
  unfold chartFin isoFin
  simp only [Iso.trans_inv, Category.assoc, hc]
  rw [pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_inv]
  erw [pullback.lift_fst_assoc]
  rw [Category.comp_id, pullbackSpecIso_inv_fst_assoc]

theorem chartFin_snd : chartFin N ℓ O ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R ℓ) (A := ↥(IgusaScheme.chartAlgFin N ℓ)) (B := O)).toRingHom) := by
  have hc : gFin N ℓ O ≫ pullback.snd (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O))) =
      pullback.snd (IgusaScheme.ιFin N ℓ) _ ≫ pullback.snd _ _ := rfl
  unfold chartFin isoFin
  simp only [Iso.trans_inv, Category.assoc, hc]
  rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackSpecIso_inv_snd]
  rfl

theorem chartFin_comp_map {O' : Type} [CommRing O'] [Algebra (DRLevel.R ℓ) O'] (φ : O →ₐ[DRLevel.R ℓ] O')
    (h₁ : IgusaScheme.igusaTo N ℓ ≫ 𝟙 _ = 𝟙 _ ≫ IgusaScheme.igusaTo N ℓ)
    (h₂ : Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O')) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O))) :
    chartFin N ℓ O' ≫ pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) h₁ h₂ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (DRLevel.R ℓ) ↥(IgusaScheme.chartAlgFin N ℓ)) φ).toRingHom) ≫
        chartFin N ℓ O := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, chartFin_fst, Category.comp_id, Category.assoc, chartFin_fst,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    simp
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, chartFin_snd, Category.assoc, chartFin_snd, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2

theorem range_chartFin : Set.range (chartFin N ℓ O).base =
    (pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O)))).base ⁻¹' Set.range (IgusaScheme.ιFin N ℓ).base := by
  rw [chartFin, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hsurj : Function.Surjective (isoFin N ℓ O).inv.base := (isoFin N ℓ O).inv.homeomorph.surjective
  rw [hsurj.range_eq, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

private noncomputable abbrev instCommRingChartAlgFinTensor :
    CommRing (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O) := inferInstance
attribute [local instance] instCommRingChartAlgFinTensor

private def _root_.OggTLevel.RingStalk.stalkIso (𝔮 : PrimeSpectrum (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) :
    (XO N ℓ O).presheaf.stalk ((chartFin N ℓ O).base 𝔮) ≅ CommRingCat.of (Localization.AtPrime 𝔮.asIdeal) :=
  asIso ((chartFin N ℓ O).stalkMap 𝔮) ≪≫ Spec.stalkIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) 𝔮

p2m_export "OggTLevel.RingStalk" "stalkIso"
theorem mem_image_top (𝔮 : PrimeSpectrum (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) :
    (chartFin N ℓ O).base 𝔮 ∈ (chartFin N ℓ O) ''ᵁ ⊤ := ⟨𝔮, trivial, rfl⟩

def sectionOf (r : ↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O) : Γ(XO N ℓ O, (chartFin N ℓ O) ''ᵁ ⊤) :=
  ((chartFin N ℓ O).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O))).inv r)

set_option maxHeartbeats 6400000 in

theorem stalkIso_germ_sectionOf (𝔮 : PrimeSpectrum (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) (r : ↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O) :
    (stalkIso N ℓ O 𝔮).hom ((XO N ℓ O).presheaf.germ ((chartFin N ℓ O) ''ᵁ ⊤) ((chartFin N ℓ O).base 𝔮)
        (mem_image_top N ℓ O 𝔮) (sectionOf N ℓ O r)) =
      algebraMap _ (Localization.AtPrime 𝔮.asIdeal) r := by
  have h1 := Scheme.Hom.germ_stalkMap (chartFin N ℓ O) ((chartFin N ℓ O) ''ᵁ ⊤) 𝔮 (mem_image_top N ℓ O 𝔮)
  have h2 := Spec.germ_stalkMapIso_hom (R := CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) 𝔮
  have h2' : ∀ s, (Spec.stalkIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) 𝔮).hom
      ((Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O))).presheaf.germ ⊤ 𝔮 trivial s) =
      algebraMap _ (Localization.AtPrime 𝔮.asIdeal) ((Scheme.ΓSpecIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O))).hom s) := by
    intro s
    have := congrArg (fun φ => φ.hom s) h2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  simp only [stalkIso, sectionOf, Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply ((XO N ℓ O).presheaf.germ _ _ (mem_image_top N ℓ O 𝔮))
    ((chartFin N ℓ O).stalkMap 𝔮), h1, ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app_apply,
    TopCat.Presheaf.germ_res_apply]
  erw [h2']
  simp

theorem isUnit_iff_of_iso {A B : CommRingCat} (e : A ≅ B) (a : A) : IsUnit a ↔ IsUnit (e.hom a) := by
  constructor
  · exact fun h => h.map e.hom.hom
  · intro h
    have := h.map e.inv.hom
    simpa using this

theorem isUnit_germ_sectionOf_iff {w : ↥(XO N ℓ O)} (𝔔 : PrimeSpectrum (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O))
    (hw : w = (chartFin N ℓ O).base 𝔔) (hwU : w ∈ (chartFin N ℓ O) ''ᵁ ⊤) (r : ↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O) :
    IsUnit ((XO N ℓ O).presheaf.germ _ w hwU (sectionOf N ℓ O r)) ↔ r ∉ 𝔔.asIdeal := by
  subst hw
  rw [isUnit_iff_of_iso (stalkIso N ℓ O 𝔔), stalkIso_germ_sectionOf]
  exact IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔.asIdeal r

theorem germ_sectionOf_mem_maximalIdeal_iff {w : ↥(XO N ℓ O)} (𝔔 : PrimeSpectrum (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O))
    (hw : w = (chartFin N ℓ O).base 𝔔) (hwU : w ∈ (chartFin N ℓ O) ''ᵁ ⊤) (r : ↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O) :
    (XO N ℓ O).presheaf.germ _ w hwU (sectionOf N ℓ O r) ∈ IsLocalRing.maximalIdeal _ ↔ r ∈ 𝔔.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_germ_sectionOf_iff N ℓ O 𝔔 hw hwU r, not_not]

theorem fst_chartFin (𝔔 : PrimeSpectrum (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[DRLevel.R ℓ] O)) :
    (pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R ℓ) O)))).base ((chartFin N ℓ O).base 𝔔) =
      (IgusaScheme.ιFin N ℓ).base (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R ℓ) (A := ↥(IgusaScheme.chartAlgFin N ℓ)) (B := O)) 𝔔) := by
  rw [← comp_base_apply', chartFin_fst, comp_base_apply']
  rfl

end RingStalk
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTLevel.RingStalk"

open RingStalk in
theorem main
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) :
    ∃ t t' : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n),
      t * t' = DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O) ^ 12 ∧
      t ∈ IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) ∧
      (IsUnit (((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hinf).hom t) ∨
        IsUnit (((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hzero).hom t)) := by
  classical
  letI : Algebra (DRLevel.R q) O := ρO.toAlgebra
  have hqP : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqP.ne_zero⟩

  set A := ↥(IgusaScheme.chartAlgFin (N₀ * q) q) with hAdef

  have hXO : DRLevel.XO (N₀ := N₀) ρO = XO (N₀ * q) q O := rfl

  obtain ⟨v, hv, hdict⟩ :=
    ModularCurve.DRModelPackageLevel.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one N₀ q hqN 𝔛
  have hmemq : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) := by
    have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
      apply IntermediateField.adjoin.mono
      rintro x ⟨d, hd, hdq, rfl⟩
      exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
    exact hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)
  obtain ⟨huA, hu'A⟩ := ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmemq
  set uF : ↥(modularFunctionFieldFull (N₀ * q)) := ⟨modularUnitSeries q, hmemq⟩ with huFdef
  have huF0 : uF ≠ 0 := by
    intro h; apply ModularCurve.modularUnitSeries_ne_zero q
    have := congrArg (fun x : ↥(modularFunctionFieldFull (N₀ * q)) => (x : LaurentSeries ℚ)) h
    simpa [huFdef] using this
  have hq0 : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by exact_mod_cast hqP.ne_zero

  have hvF : (v : ↥(modularFunctionFieldFull (N₀ * q))) = uF ∨
      (v : ↥(modularFunctionFieldFull (N₀ * q))) = ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹ := by
    rcases hv with hv | hv
    · left; exact Subtype.ext hv
    · right; apply Subtype.ext
      rw [hv]
      push_cast
      rfl

  have hv'mem : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * (v : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ∈
      IgusaScheme.chartAlgFin (N₀ * q) q := by
    rcases hvF with h | h
    · rw [h]; exact_mod_cast hu'A
    · rw [h, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), one_mul]
      exact huA
  set v' : A := ⟨_, hv'mem⟩ with hv'def
  have hv0 : (v : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by
    rcases hvF with h | h
    · rw [h]; exact huF0
    · rw [h]; exact mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero huF0)
  have hvv' : v * v' = ((q : ℕ) : A) ^ 12 := by
    apply Subtype.ext
    show (v : ↥(modularFunctionFieldFull (N₀ * q))) * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * (v : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹) = _
    rw [mul_comm (v : ↥(modularFunctionFieldFull (N₀ * q))) _, mul_assoc, inv_mul_cancel₀ hv0, mul_one]
    push_cast
    rfl

  obtain ⟨W, hW₀, hW₁, hne, habove, hcomplete⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
  obtain ⟨P, hPmem, hPprime, hPne, hmin⟩ :=
    ModularCurve.DRModelPackageLevel.exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair N₀ q hqN W hW₀ hW₁ hne habove hcomplete
  obtain ⟨-, -, ⟨huW0, huinvW0⟩, ⟨hu'W1, hu'invW1⟩⟩ :=
    ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd N₀ q hqN hmemq (W 0) (W 1) hW₀ hW₁
  have hexP : ∃ i : Fin 2, v ∉ P i := by
    rcases hvF with h | h
    · refine ⟨0, fun hP => ?_⟩
      have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 0 v).mp hP)
      rw [h] at hlt
      have hle : (W 0).valuation (uF)⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr huinvW0
      rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact huF0)] at hle
      exact not_lt.mpr hle hlt
    · refine ⟨1, fun hP => ?_⟩
      have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 1 v).mp hP)
      rw [h] at hlt

      have heq : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹ = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹ := by
        rw [mul_inv, inv_inv, mul_comm (uF⁻¹) _]
      rw [heq, map_inv₀] at hlt
      have hle : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) ≤ 1 :=
        ((W 1).valuation_le_one_iff _).mpr hu'W1
      have hle' : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹ ≤ 1 :=
        ((W 1).valuation_le_one_iff _).mpr hu'invW1
      rw [map_inv₀] at hle'
      have hpos : 0 < (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) := by
        rw [Valuation.pos_iff]; exact mul_ne_zero huF0 (inv_ne_zero (pow_ne_zero _ hq0))
      rw [inv_le_one₀ hpos] at hle'
      have h1 : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) = 1 := le_antisymm hle hle'
      rw [h1, inv_one] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨i₀, hvP⟩ := hexP
  haveI := hPprime i₀
  have hqP' : ((q : ℕ) : A) ∈ P i₀ := (hPmem i₀ _).2 (by first | simpa using (habove i₀).1 | exact_mod_cast (habove i₀).1 | exact (habove i₀).1)

  haveI : IsLocalRing (DRLevel.R q) := GaloisRep.ratLocalizedAt.isLocalRing hqP
  have hmaxR : IsLocalRing.maximalIdeal (DRLevel.R q) = Ideal.span {((q : ℕ) : DRLevel.R q)} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hqP
  have hcomap_eq : ∀ (I : Ideal (DRLevel.R q)), I.IsPrime → ((q : ℕ) : DRLevel.R q) ∈ I → I = IsLocalRing.maximalIdeal (DRLevel.R q) := by
    intro I hI hqI
    refine le_antisymm (IsLocalRing.le_maximalIdeal hI.ne_top) ?_
    rw [hmaxR, Ideal.span_singleton_le_iff_mem]
    exact hqI
  set xP : ↥(DRLevel.X N₀ q) := (IgusaScheme.ιFin (N₀ * q) q).base ⟨P i₀, hPprime i₀⟩ with hxP
  have hbase : (DRLevel.toBase N₀ q).base xP = (Spec.map (CommRingCat.ofHom (toκ.comp ρO))).base (IsLocalRing.closedPoint κ) := by
    rw [hxP, ← comp_base_apply', show DRLevel.toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q from rfl,
      IgusaScheme.ιFin_igusaTo]
    apply PrimeSpectrum.ext
    show Ideal.comap _ (P i₀) = Ideal.comap _ _
    rw [hcomap_eq _ (Ideal.comap_isPrime _ (P i₀)) (by simpa [Ideal.mem_comap] using hqP')]
    symm
    refine hcomap_eq _ (Ideal.comap_isPrime _ _) ?_
    show (toκ.comp ρO) ((q : ℕ) : DRLevel.R q) ∈ (IsLocalRing.closedPoint κ).asIdeal
    rw [map_natCast, CharP.cast_eq_zero]
    exact Ideal.zero_mem _
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := DRLevel.toBase N₀ q)
    (g := Spec.map (CommRingCat.ofHom (toκ.comp ρO))) xP (IsLocalRing.closedPoint κ) hbase

  obtain ⟨⟨z₀, hz₀⟩, -⟩ := hdict κ (toκ.comp ρO) y ⟨P i₀, hPprime i₀⟩ hy hvP

  letI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  set bc := DRLevel.bcMap (N₀ := N₀) ρO toκ with hbc
  have hbc_fst : bc ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [hbc, DRLevel.bcMap, pullback.lift_fst, Category.comp_id]
  set U : (DRLevel.XO (N₀ := N₀) ρO).Opens := (chartFin (N₀ * q) q O) ''ᵁ ⊤ with hU
  have hUrange : ∀ w : ↥(DRLevel.XO (N₀ := N₀) ρO), w ∈ U ↔
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base w ∈ Set.range (IgusaScheme.ιFin (N₀ * q) q).base := by
    intro w
    have := range_chartFin (N₀ * q) q O
    constructor
    · rintro ⟨𝔔, -, rfl⟩
      have h1 : (chartFin (N₀ * q) q O).base 𝔔 ∈ Set.range (chartFin (N₀ * q) q O).base := ⟨𝔔, rfl⟩
      rw [this] at h1
      exact h1
    · intro hw
      have h1 : w ∈ Set.range (chartFin (N₀ * q) q O).base := by rw [this]; exact hw
      obtain ⟨𝔔, h𝔔⟩ := h1
      exact ⟨𝔔, trivial, h𝔔⟩
  have hxU : 𝔛.crossingPt ρO toκ n ∈ U := by
    rw [hUrange]
    obtain ⟨z, -, hz⟩ := ModularCurve.DRModelPackageLevel.crossingPt_mem_preimage_iotaFin N₀ q hqN 𝔛 O ρO κ toκ n
    exact ⟨z, hz⟩
  have hinfU : 𝔛.ξinf ρO toκ ∈ U := hinf.mem_open U.isOpen hxU
  have hzeroU : 𝔛.ξzero ρO toκ ∈ U := hzero.mem_open U.isOpen hxU

  have hchart : ∀ w : ↥(DRLevel.XO (N₀ := N₀) ρO), w ∈ U → ∃ 𝔔 : PrimeSpectrum (A ⊗[DRLevel.R q] O),
      w = (chartFin (N₀ * q) q O).base 𝔔 ∧
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base w =
        (IgusaScheme.ιFin (N₀ * q) q).base (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := A) (B := O)) 𝔔) := by
    rintro w ⟨𝔔, -, rfl⟩
    exact ⟨𝔔, rfl, fst_chartFin (N₀ * q) q O 𝔔⟩

  refine ⟨(DRLevel.XO (N₀ := N₀) ρO).presheaf.germ U (𝔛.crossingPt ρO toκ n) hxU (sectionOf (N₀ * q) q O (v ⊗ₜ[DRLevel.R q] (1 : O))),
    (DRLevel.XO (N₀ := N₀) ρO).presheaf.germ U (𝔛.crossingPt ρO toκ n) hxU (sectionOf (N₀ * q) q O (v' ⊗ₜ[DRLevel.R q] (1 : O))), ?_, ?_, ?_⟩
  ·
    set G := (DRLevel.XO (N₀ := N₀) ρO).presheaf.germ U (𝔛.crossingPt ρO toκ n) hxU with hG
    show G.hom _ * G.hom _ = _
    rw [← map_mul G.hom]
    have hsec : sectionOf (N₀ * q) q O (v ⊗ₜ[DRLevel.R q] (1 : O)) * sectionOf (N₀ * q) q O (v' ⊗ₜ[DRLevel.R q] (1 : O)) =
        ((q : ℕ) : Γ(DRLevel.XO (N₀ := N₀) ρO, U)) ^ 12 := by
      simp only [sectionOf, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hvv']
      have hincl : ((((q : ℕ) : A) ^ 12) ⊗ₜ[DRLevel.R q] (1 : O) : A ⊗[DRLevel.R q] O) =
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[DRLevel.R q] O) (((q : ℕ) : A) ^ 12) := rfl
      simp only [hincl, map_pow, map_natCast]
    rw [hsec, map_pow, map_natCast]
    simp only [DRModelPackageLevel.baseGerm, map_natCast]
  ·
    obtain ⟨𝔔₁, h𝔔₁, hfst₁⟩ := hchart _ hzeroU
    have hvQ : v ⊗ₜ[DRLevel.R q] (1 : O) ∈ 𝔔₁.asIdeal := by

      set y₁ : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)) := (𝔛.comp κ (toκ.comp ρO) 1).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) with hy₁
      have hξ : 𝔛.ξzero ρO toκ = bc.base y₁ := rfl
      have hfst_y : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base y₁ =
          (IgusaScheme.ιFin (N₀ * q) q).base (PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := A) (B := O)) 𝔔₁) := by
        rw [← hfst₁, hξ, ← comp_base_apply' bc, hbc_fst]
      by_contra hv1
      have := (hdict κ (toκ.comp ρO) y₁ _ hfst_y (by
        intro hmem; apply hv1
        show Algebra.TensorProduct.includeLeftRingHom v ∈ 𝔔₁.asIdeal
        exact hmem)).2
      exact this ⟨genericPoint _, hy₁.symm⟩
    have hzero_mem := (germ_sectionOf_mem_maximalIdeal_iff (N₀ * q) q O 𝔔₁ h𝔔₁ hzeroU _).mpr hvQ

    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h2 := hunit.map ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hzero).hom
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp hzero_mem h2
  ·
    left
    set w := bc.base y with hw
    have hwU : w ∈ U := by
      rw [hUrange, hw, ← comp_base_apply' bc, hbc_fst, hy]
      exact ⟨_, rfl⟩
    obtain ⟨𝔔, h𝔔, hfst⟩ := hchart w hwU
    have hPQ : PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := A) (B := O)) 𝔔 = ⟨P i₀, hPprime i₀⟩ := by
      apply (IgusaScheme.ιFin (N₀ * q) q).isOpenEmbedding.injective
      rw [← hfst, hw, ← comp_base_apply' bc, hbc_fst, hy]
    have hvQ : v ⊗ₜ[DRLevel.R q] (1 : O) ∉ 𝔔.asIdeal := by
      intro hmem
      apply hvP
      have : v ∈ (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := A) (B := O)) 𝔔).asIdeal := hmem
      rw [hPQ] at this
      exact this
    have hunit_w : IsUnit ((DRLevel.XO (N₀ := N₀) ρO).presheaf.germ U w hwU (sectionOf (N₀ * q) q O (v ⊗ₜ[DRLevel.R q] (1 : O)))) :=
      (isUnit_germ_sectionOf_iff (N₀ * q) q O 𝔔 h𝔔 hwU _).mpr hvQ

    have hgen : 𝔛.ξinf ρO toκ ⤳ w := by
      have h1 : genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) ⤳ z₀ := genericPoint_specializes z₀
      have h2 := (h1.map (𝔛.comp κ (toκ.comp ρO) 0).base.hom.continuous).map bc.base.hom.continuous
      rw [hz₀] at h2
      exact h2
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    have h3 := hunit_w.map ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hgen).hom
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h3
    exact h3

end OggTLevel
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTLevel.RingStalk P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTLevel"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTLevel.RingStalk P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggTLevel"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) :
    ∃ t t' : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n),
      t * t' = DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O) ^ 12 ∧
      t ∈ IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) ∧
      (IsUnit (((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hinf).hom t) ∨
        IsUnit (((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hzero).hom t)) :=
  OggTLevel.main N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero

end S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing (solution)
