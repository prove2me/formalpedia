-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/31eed740-a0fa-5f2f-bf8a-15ec21d0b6ed

import Mathlib
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_DRModelPackage_exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero
import Theorems.Thm_ModularCurve_DRModelPackage_iotaFin_mem_smoothLocus_of_aeval_mem
import Theorems.Thm_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
import Theorems.Thm_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve AlgebraicCurve IsLocalRing"

p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve AlgebraicCurve"
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard

namespace ModularCurve
p2m_export "ModularCurve" "HpoolLevelRing.exists_finite_etale_levelRing_self modularUnitSeries modularFunctionFieldFull HpoolLevelRing.neZero_of_fact_prime HpoolLevelRing.Afin HpoolLevelRing.AfinAway HpoolLevelRing.levelRing IgusaScheme.jFull IgusaScheme DRModelPackage.exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero DRModel DRModel.toBase DRModelPackage DRModelPackage.iotaFin_mem_smoothLocus_of_aeval_mem DRModelPackage.mem_connectedComponentIn_of_aeval_mem IgusaScheme.geometricallyConnected_toBase_int modularUnitSeries_mem_modularFunctionFieldFull"
namespace HpoolGeo
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime] (f : ℤ)

attribute [local instance] HpoolLevelRing.neZero_of_fact_prime

set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull p)
set_option quotPrecheck false in
local notation "jj" => IgusaScheme.jFull p
set_option quotPrecheck false in
local notation "LL" => Localization.Away f
set_option quotPrecheck false in
local notation "AA" => HpoolLevelRing.Afin p
set_option quotPrecheck false in
local notation "AF" => HpoolLevelRing.AfinAway p f

theorem algebraMap_comp_eq :
    (algebraMap LL AF).comp (algebraMap ℤ LL) = (algebraMap AA AF).comp (algebraMap ℤ AA) :=
  RingHom.ext_int _ _

noncomputable def ιL : Spec (CommRingCat.of AF) ⟶ pullback (DRModel.toBase p) (specMap ℤ LL) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap AA AF)) ≫ TwoChartIntegralModel.ιFin ℤ FF jj)
    (Spec.map (CommRingCat.ofHom (algebraMap LL AF)))
    (by
      rw [Category.assoc]
      erw [TwoChartIntegralModel.ιFin_toBase]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        algebraMap_comp_eq])

@[scoped simp] theorem ιL_fst :
    ιL p f ≫ pullback.fst (DRModel.toBase p) (specMap ℤ LL) =
      Spec.map (CommRingCat.ofHom (algebraMap AA AF)) ≫ TwoChartIntegralModel.ιFin ℤ FF jj :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem ιL_snd :
    ιL p f ≫ pullback.snd (DRModel.toBase p) (specMap ℤ LL) = Spec.map (CommRingCat.ofHom (algebraMap LL AF)) :=
  pullback.lift_snd _ _ _

theorem ιL_baseChange :
    ιL p f ≫ baseChange ℤ (DRModel.toBase p) LL = Spec.map (CommRingCat.ofHom (algebraMap LL AF)) :=
  ιL_snd p f

scoped instance isOpenImmersion_specMap_away : IsOpenImmersion (specMap ℤ LL) :=
  IsOpenImmersion.of_isLocalization f

scoped instance isOpenImmersion_ιL : IsOpenImmersion (ιL p f) := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap AA AF))) :=
    IsOpenImmersion.of_isLocalization (algebraMap ℤ AA f)
  have h2 : IsOpenImmersion (ιL p f ≫ pullback.fst (DRModel.toBase p) (specMap ℤ LL)) := by
    rw [ιL_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (DRModel.toBase p) (specMap ℤ LL))

noncomputable def zOf (I : Ideal AF) : Spec (CommRingCat.of (AF ⧸ I)) ⟶ pullback (DRModel.toBase p) (specMap ℤ LL) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ιL p f

theorem zOf_baseChange (I : Ideal AF) :
    zOf p f I ≫ baseChange ℤ (DRModel.toBase p) LL = specMap LL (AF ⧸ I) := by
  rw [zOf, Category.assoc, ιL_baseChange, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isClosedImmersion_zOf (I : Ideal AF) [Module.Finite LL (AF ⧸ I)]
    [IsSeparated (DRModel.toBase p)] : IsClosedImmersion (zOf p f I) := by
  have hmono : Mono (zOf p f I) := by
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    unfold zOf; infer_instance
  have hfin : IsFinite (specMap LL (AF ⧸ I)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hproper : IsProper (zOf p f I) := by
    have : IsProper (zOf p f I ≫ baseChange ℤ (DRModel.toBase p) LL) := by
      rw [zOf_baseChange]; infer_instance
    exact IsProper.of_comp _ (baseChange ℤ (DRModel.toBase p) LL)
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hproper, hmono⟩

theorem disjoint_range_zOf {I J : Ideal AF} (hIJ : I ⊔ J = ⊤) :
    Disjoint (Set.range (zOf p f I).base) (Set.range (zOf p f J).base) := by
  have hinj : Function.Injective (ιL p f).base := (ιL p f).isOpenEmbedding.injective
  have hr : ∀ K : Ideal AF, Set.range (zOf p f K).base =
      (ιL p f).base '' (PrimeSpectrum.zeroLocus (K : Set AF)) := by
    intro K
    have hc : ⇑(zOf p f K) = ⇑(ιL p f) ∘ ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := rfl
    rw [hc, Set.range_comp]
    congr 1
    have := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := K))
    rw [Ideal.mk_ker] at this
    exact this
  rw [hr, hr, Set.disjoint_image_iff hinj]
  refine Set.disjoint_iff_inter_eq_empty.mpr ?_
  rw [← PrimeSpectrum.zeroLocus_sup, hIJ]
  exact PrimeSpectrum.zeroLocus_empty_of_one_mem (show (1 : AF) ∈ ((⊤ : Ideal AF) : Set AF) from trivial)

theorem mem_smoothLocus_of_not_mem (𝔛 : DRModelPackage p) (x : ↥(DRModel p))
    (hx : ((DRModel.toBase p).base x) ∈ PrimeSpectrum.basicOpen (p : ℤ)) : x ∈ 𝔛.smoothLocus := by

  let ιp : Spec (CommRingCat.of (Localization.Away (p : ℤ))) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))
  haveI : IsOpenImmersion ιp := IsOpenImmersion.of_isLocalization (p : ℤ)
  let g := pullback.fst (DRModel.toBase p) ιp
  let U : (DRModel p).Opens := Scheme.Hom.opensRange g
  have hsm : Smooth (U.ι ≫ DRModel.toBase p) := by

    haveI : Smooth (pullback.snd (DRModel.toBase p) ιp) := 𝔛.smooth_away
    have hU : U.ι = (Scheme.Hom.isoOpensRange g).inv ≫ g :=
      (Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι g)
    have hfac : U.ι ≫ DRModel.toBase p = (Scheme.Hom.isoOpensRange g).inv ≫ pullback.snd (DRModel.toBase p) ιp ≫ ιp := by
      rw [hU, Category.assoc]
      congr 1
      exact pullback.condition
    rw [hfac]
    infer_instance
  have hU : U ≤ 𝔛.smoothLocus := 𝔛.smoothLocus_maximal U hsm
  apply hU

  show x ∈ Set.range g.base
  rw [Scheme.Pullback.range_fst]
  show (DRModel.toBase p).base x ∈ Set.range ιp.base
  have : Set.range ιp.base = (PrimeSpectrum.basicOpen (p : ℤ) : Set (PrimeSpectrum ℤ)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away (p : ℤ)) (p : ℤ)
  rw [this]
  exact hx

theorem sup_span_aeval_eq_top (v : AA) {g₁ g₂ : Polynomial ℤ}
    (h : IsCoprime (g₁.map (algebraMap ℤ LL)) (g₂.map (algebraMap ℤ LL))) :
    Ideal.span {Polynomial.aeval (algebraMap AA AF v) g₁} ⊔ Ideal.span {Polynomial.aeval (algebraMap AA AF v) g₂} =
      (⊤ : Ideal AF) := by
  set x := algebraMap AA AF v
  have key : ∀ g : Polynomial ℤ, Polynomial.aeval x (g.map (algebraMap ℤ LL)) = Polynomial.aeval x g := by
    intro g
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have hc := h.map (Polynomial.aeval x : Polynomial LL →ₐ[LL] AF).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, key] at hc
  exact Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_span_singleton_iff _ _).mpr hc)

omit [Fact p.Prime] in

theorem specMap_point_mem_basicOpen (k : Type) [Field k] (hk : (p : k) ≠ 0)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)) (t : ↥(Spec (CommRingCat.of k))) :
    s.base t ∈ PrimeSpectrum.basicOpen (p : ℤ) := by
  rw [← Spec.map_preimage s]
  show (p : ℤ) ∉ (PrimeSpectrum.comap (Spec.preimage s).hom t).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, eq_intCast]
  intro h
  apply hk
  have : t.asIdeal = ⊥ := by
    haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
    rw [Subsingleton.elim t (⊥ : PrimeSpectrum k)]
    rfl
  rw [this] at h
  simpa using h

theorem mem_smoothLocus_and_mem_connectedComponentIn_of_cast_ne_zero (𝔛 : DRModelPackage p)
    (k : Type) [Field k] (hk : (p : k) ≠ 0) (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ))
    (y x₀ : ↥(pullback (DRModel.toBase p) s)) :
    (pullback.fst (DRModel.toBase p) s).base y ∈ 𝔛.smoothLocus ∧
      y ∈ connectedComponentIn
        ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) :
          Set ↥(pullback (DRModel.toBase p) s)) x₀ := by
  have hall : ∀ z : ↥(pullback (DRModel.toBase p) s), (pullback.fst (DRModel.toBase p) s).base z ∈ 𝔛.smoothLocus := by
    intro z
    apply mem_smoothLocus_of_not_mem p 𝔛
    have : (DRModel.toBase p).base ((pullback.fst (DRModel.toBase p) s).base z) =
        s.base ((pullback.snd (DRModel.toBase p) s).base z) := by
      change (pullback.fst (DRModel.toBase p) s ≫ DRModel.toBase p).base z = (pullback.snd (DRModel.toBase p) s ≫ s).base z
      rw [pullback.condition]
    rw [this]
    exact specMap_point_mem_basicOpen p k hk s _
  refine ⟨hall y, ?_⟩
  have htop : ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) :
      Set ↥(pullback (DRModel.toBase p) s)) = Set.univ :=
    Set.eq_univ_of_forall fun z => hall z
  rw [htop, connectedComponentIn_univ]
  haveI : GeometricallyConnected (DRModel.toBase p) := ModularCurve.IgusaScheme.geometricallyConnected_toBase_int p
  haveI : ConnectedSpace ↥(pullback (DRModel.toBase p) s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (DRModel.toBase p) s)
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact Set.mem_univ y

omit [Fact p.Prime] in

theorem mem_basicOpen_of_dvd {f : ℤ} (hpf : (p : ℤ) ∣ f) (x : PrimeSpectrum ℤ)
    (hx : x ∈ PrimeSpectrum.basicOpen f) : x ∈ PrimeSpectrum.basicOpen (p : ℤ) :=
  fun h => hx (by
    obtain ⟨c, rfl⟩ := hpf
    exact x.asIdeal.mul_mem_right c h)

theorem connectedComponentIn_smoothLocus_eq_univ_of_dvd (𝔛 : DRModelPackage p) (f : ℤ) (hpf : (p : ℤ) ∣ f)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    connectedComponentIn
      (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
      (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) = Set.univ := by
  set g := pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫
    pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) with hg
  have hall : ∀ y, g.base y ∈ 𝔛.smoothLocus := by
    intro y
    apply mem_smoothLocus_of_not_mem p 𝔛
    have hfac : g ≫ DRModel.toBase p =
        (pullback.snd (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ s) ≫ specMap ℤ (Localization.Away f) := by
      rw [hg, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
    have : (DRModel.toBase p).base (g.base y) =
        (specMap ℤ (Localization.Away f)).base ((pullback.snd _ s ≫ s).base y) := by
      change (g ≫ DRModel.toBase p).base y = _
      rw [hfac]
      rfl
    rw [this]
    apply mem_basicOpen_of_dvd p hpf
    have hr : Set.range (specMap ℤ (Localization.Away f)).base = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum ℤ)) :=
      PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
    have hm := Set.mem_range_self (f := (specMap ℤ (Localization.Away f)).base) ((pullback.snd _ s ≫ s).base y)
    rw [hr] at hm
    exact hm
  have htop : (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s)) = Set.univ :=
    Set.eq_univ_of_forall fun y => hall y
  rw [htop, connectedComponentIn_univ]
  haveI : GeometricallyConnected (DRModel.toBase p) := ModularCurve.IgusaScheme.geometricallyConnected_toBase_int p
  haveI : ConnectedSpace ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s)
  exact PreconnectedSpace.connectedComponent_eq_univ _

theorem exists_prime_of_mem_range_zOf (v : HpoolLevelRing.Afin p) (g : Polynomial ℤ)
    {x : ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))}
    (hx : x ∈ Set.range (zOf p f (Ideal.span {Polynomial.aeval (algebraMap _ (HpoolLevelRing.AfinAway p f) v) g})).base) :
    ∃ 𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p),
      (pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base x =
        (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 ∧
      Polynomial.aeval v g ∈ 𝔮.asIdeal := by
  set I : Ideal AF := Ideal.span {Polynomial.aeval (algebraMap AA AF v) g} with hI
  obtain ⟨pt, rfl⟩ := hx
  let ψ : AA →+* AF ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap AA AF)
  refine ⟨PrimeSpectrum.comap ψ pt, ?_, ?_⟩
  · have h1 : (zOf p f I ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) =
        Spec.map (CommRingCat.ofHom ψ) ≫ TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := by
      rw [zOf, Category.assoc, ιL_fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h2 := congrArg (fun φ => φ.base pt) h1
    exact h2
  · show ψ (Polynomial.aeval v g) ∈ pt.asIdeal
    have : ψ (Polynomial.aeval v g) = 0 := by
      simp only [ψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      have hc : algebraMap AA AF (Polynomial.aeval v g) = Polynomial.aeval (algebraMap AA AF v) g := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
        congr 1 <;> exact RingHom.ext_int _ _
      rw [hc, hI]
      exact Ideal.subset_span rfl
    rw [this]; exact zero_mem _

end ModularCurve.HpoolGeo
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve.HpoolGeo"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve"

namespace HpoolAsm

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem not_dvd_of_natDegree_lt {g c₀ : ℤ[X]} (hc₀ : c₀ ≠ 0) (h : c₀.natDegree < g.natDegree) : ¬ g ∣ c₀ :=
  fun hdvd => (Nat.lt_irrefl _) (lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvd hc₀) h)

theorem not_dvd_prod_of_forall {p : ℕ} (hp : p.Prime) {ι : Type} (s : Finset ι) (c : ι → ℤ)
    (h : ∀ i ∈ s, ¬ (p : ℤ) ∣ c i) : ¬ (p : ℤ) ∣ ∏ i ∈ s, c i := by
  intro hdvd
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff_prime_int.mp hp) _).mp hdvd
  exact h i hi hpi

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem not_dvd_resultant_and_isCoprime_map (p : ℕ) [Fact p.Prime] {D : ℕ} {g₁ g₂ : ℤ[X]}
    (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hD₁ : g₁.natDegree = D) (hD₂ : g₂.natDegree = D)
    (hcop : IsCoprime (g₁.map (Int.castRingHom (ZMod p))) (g₂.map (Int.castRingHom (ZMod p)))) :
    ¬ (p : ℤ) ∣ Polynomial.resultant g₁ g₂ D D ∧
    ∀ (R : Type) [CommRing R] [Algebra ℤ R], IsUnit (algebraMap ℤ R (Polynomial.resultant g₁ g₂ D D)) →
      IsCoprime (g₁.map (algebraMap ℤ R)) (g₂.map (algebraMap ℤ R)) := by
  have hp : p.Prime := Fact.out
  constructor
  · intro hdvd
    have hu : IsUnit (Polynomial.resultant (g₁.map (Int.castRingHom (ZMod p))) (g₂.map (Int.castRingHom (ZMod p)))) :=
      (isUnit_resultant_iff_isCoprime (hg₁.map _)).mpr hcop
    rw [hg₁.natDegree_map (Int.castRingHom (ZMod p)), hg₂.natDegree_map (Int.castRingHom (ZMod p)),
      hD₁, hD₂, resultant_map_map] at hu
    exact hu.ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd)
  · intro R _ _ hunit
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact ⟨0, 0, Subsingleton.elim _ _⟩
    have key := (isUnit_resultant_iff_isCoprime (g := g₂.map (algebraMap ℤ R)) (hg₁.map (algebraMap ℤ R)))
    rw [hg₁.natDegree_map (algebraMap ℤ R), hg₂.natDegree_map (algebraMap ℤ R), hD₁, hD₂,
      resultant_map_map] at key
    exact key.mp hunit

theorem exists_prime_ne_of_not_le {p : ℕ} (𝔭 : PrimeSpectrum ℤ) (h : ¬ 𝔭.asIdeal ≤ Ideal.span {(p : ℤ)}) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ 𝔭.asIdeal ≤ Ideal.span {(ℓ : ℤ)} := by
  have hne : 𝔭.asIdeal ≠ ⊥ := fun hb => h (hb ▸ bot_le)
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal hne
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal 𝔭.asIdeal).principal
  have ha' : 𝔭.asIdeal = Ideal.span {a} := ha
  have hpa : Prime a := by
    rw [← Ideal.span_singleton_prime (by rintro rfl; simp [ha'] at hne), ← ha']
    exact 𝔭.isPrime
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hpa, ?_, ?_⟩
  · rintro habs
    apply h
    rw [ha', ← Int.span_natAbs, habs]
  · rw [ha', Int.span_natAbs]

end HpoolAsm
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime.ModularCurve.HpoolGeo"

theorem HpoolAsm.tail (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ)
    (f : ℤ) (hf𝔭 : f ∉ 𝔭.asIdeal) (v : HpoolLevelRing.Afin p) (cdeg D M : ℕ) (g : Fin M → Polynomial ℤ)
    (hM : A₀ * (cdeg * D) ^ n₀ + B₀ < M) (hdeg1 : 1 ≤ cdeg * D)
    (hfin : ∀ i, Module.Finite (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)))
    (het : ∀ i, Algebra.Etale (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)))
    (hrank : ∀ i (𝔮 : PrimeSpectrum (Localization.Away f)),
      Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) 𝔮 = cdeg * D)
    (z : ∀ i, Spec (CommRingCat.of (HpoolLevelRing.levelRing p f v (g i))) ⟶
      pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (hzci : ∀ i, IsClosedImmersion (z i))
    (hzbase : ∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) =
      specMap (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)))
    (hsmooth : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus :
        (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))))
    (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hcomp : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) :
    ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by
  classical
  haveI := hfin; haveI := het
  let deg : Fin M → ℕ := fun _ => cdeg * D
  have hdeg : ∀ i, Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) = deg i :=
    fun i => funext (hrank i)
  obtain ⟨R', _, _, finR, etR, ffR, hφ⟩ :=
    Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi (Localization.Away f)
      (fun i => HpoolLevelRing.levelRing p f v (g i)) deg hdeg
  refine ⟨f, hf𝔭, cdeg * D, M, hM, R', inferInstance, inferInstance, ‹Algebra (Localization.Away f) R'›, ?_,
    finR, etR, ffR, fun i => HpoolLevelRing.levelRing p f v (g i), inferInstance, inferInstance, hfin, het, deg,
    fun _ => hdeg1, fun _ => le_refl _, fun i => (hφ i).some, z, hzci, hzbase, hsmooth, hdisj, hcomp⟩
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (RingHom.congr_fun (Subsingleton.elim ((algebraMap (Localization.Away f) R').comp
      (algebraMap ℤ (Localization.Away f))) (algebraMap ℤ R')) x).symm

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p) (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ)
    (h𝔭p : 𝔭.asIdeal ≤ Ideal.span {(p : ℤ)}) :
    ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by
  classical
  have hpr : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpr.ne_zero⟩
  have hmem : modularUnitSeries p ∈ modularFunctionFieldFull p :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p

  obtain ⟨v, hv, hdict⟩ :=
    ModularCurve.DRModelPackage.exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero p hp 𝔛 hmem

  obtain ⟨avoid, havoid, hXavoid, c₀, hc₀, hlevel⟩ :=
    ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self p hp hmem v hv

  obtain ⟨D, M, g, hD2, hDc₀, hM, hmonic, hirr, hsep, hcop, havd, h0⟩ :=
    Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime p n₀ A₀ B₀ (p - 1) (c₀.natDegree + 1)
      avoid havoid

  have hndvd : ∀ i, ¬ g i ∣ c₀ := fun i =>
    HpoolAsm.not_dvd_of_natDegree_lt hc₀ (by rw [(hmonic i).2]; omega)
  have hdeg1g : ∀ i, 1 ≤ (g i).natDegree := fun i => by rw [(hmonic i).2]; omega
  choose c hcp hc0 hcgood using fun i => hlevel (g i) (hmonic i).1 (hdeg1g i) (hirr i) (havd i) (hndvd i)

  have hres := fun (q : Fin M × Fin M) (hq : q.1 ≠ q.2) =>
    HpoolAsm.not_dvd_resultant_and_isCoprime_map p (hmonic q.1).1 (hmonic q.2).1 (hmonic q.1).2 (hmonic q.2).2
      (hcop q.1 q.2 hq)

  let pairs : Finset (Fin M × Fin M) := Finset.univ.filter fun q => q.1 ≠ q.2
  let f : ℤ := (∏ i, c i) * ∏ q ∈ pairs, Polynomial.resultant (g q.1) (g q.2) D D
  have hpf : ¬ (p : ℤ) ∣ f := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hpr).dvd_mul.mp h with h1 | h2
    · exact HpoolAsm.not_dvd_prod_of_forall hpr _ _ (fun i _ => hcp i) h1
    · exact HpoolAsm.not_dvd_prod_of_forall hpr _ _ (fun q hq => (hres q (Finset.mem_filter.mp hq).2).1) h2
  have hf0 : f ≠ 0 := fun h => hpf (h ▸ dvd_zero _)
  have hcf : ∀ i, c i ∣ f := fun i => Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  have hresf : ∀ i j, i ≠ j → Polynomial.resultant (g i) (g j) D D ∣ f := fun i j hij =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : Fin M × Fin M => Polynomial.resultant (g q.1) (g q.2) D D)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩)) _
  have hf𝔭 : f ∉ 𝔭.asIdeal := fun h => hpf (Ideal.mem_span_singleton.mp (h𝔭p h))

  have hgood := fun i => hcgood i f hf0 (hcf i)
  have hfin : ∀ i, Module.Finite (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) := fun i => (hgood i).1
  have het : ∀ i, Algebra.Etale (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) := fun i => (hgood i).2.1
  have hrank : ∀ i (𝔮 : PrimeSpectrum (Localization.Away f)),
      Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) 𝔮 = (p - 1) * D := by
    intro i 𝔮; rw [(hgood i).2.2.2.2 𝔮, (hmonic i).2]

  haveI : IsSeparated (DRModel.toBase p) := by haveI := 𝔛.isProper; infer_instance
  haveI := hfin
  let z : ∀ i, Spec (CommRingCat.of (HpoolLevelRing.levelRing p f v (g i))) ⟶
      pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)) :=
    fun i => ModularCurve.HpoolGeo.zOf p f (Ideal.span {Polynomial.aeval (algebraMap _ (HpoolLevelRing.AfinAway p f) v) (g i)})
  have hzci : ∀ i, IsClosedImmersion (z i) := fun i => ModularCurve.HpoolGeo.isClosedImmersion_zOf p f _
  have hzbase : ∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) =
      specMap (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) :=
    fun i => ModularCurve.HpoolGeo.zOf_baseChange p f _
  have hsup : ∀ i j, i ≠ j →
      Ideal.span {Polynomial.aeval (algebraMap _ (HpoolLevelRing.AfinAway p f) v) (g i)} ⊔
        Ideal.span {Polynomial.aeval (algebraMap _ (HpoolLevelRing.AfinAway p f) v) (g j)} = ⊤ := by
    intro i j hij
    apply ModularCurve.HpoolGeo.sup_span_aeval_eq_top p f v
    exact (hres (i, j) hij).2 (Localization.Away f)
      (isUnit_of_dvd_unit (map_dvd (algebraMap ℤ (Localization.Away f)) (hresf i j hij))
        (IsLocalization.Away.algebraMap_isUnit f))
  have hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base) :=
    fun i j hij => ModularCurve.HpoolGeo.disjoint_range_zOf p f (hsup i j hij)

  have hg0 : ∀ i, ¬ (p : ℤ) ∣ (g i).coeff 0 := by
    intro i hdvd
    apply h0 i
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd

  have hsmooth : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus :
        (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))) := by
    intro i x hx
    obtain ⟨𝔮, h1, h2⟩ := ModularCurve.HpoolGeo.exists_prime_of_mem_range_zOf p f v (g i) hx
    show (pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base x ∈ (𝔛.smoothLocus : Set _)
    rw [h1]
    exact ModularCurve.DRModelPackage.iotaFin_mem_smoothLocus_of_aeval_mem p 𝔛 v hdict (g i) (hg0 i) 𝔮 h2
  have hcomp : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by
    intro k _ _ s i y hy
    obtain ⟨𝔮, h1, h2⟩ := ModularCurve.HpoolGeo.exists_prime_of_mem_range_zOf p f v (g i) hy
    refine ModularCurve.DRModelPackage.mem_connectedComponentIn_of_aeval_mem p 𝔛 v hdict (g i) (hg0 i) f k s y 𝔮 ?_ h2
    rw [← h1]
    rfl

  have hdeg1 : 1 ≤ (p - 1) * D := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact HpoolAsm.tail p 𝔛 𝔭 A₀ B₀ n₀ f hf𝔭 v (p - 1) D M g hM hdeg1 hfin het hrank z hzci hzbase hsmooth hdisj hcomp

end S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_prime (solution)
