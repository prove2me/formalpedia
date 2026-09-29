-- Prove2me | solution 1 for ModularCurve.slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f9293d09-4609-5aa8-9f1b-ca3606fe0909

import Mathlib
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
import Theorems.Thm_ModularCurve_NodeLocalized_gaussData_nodeCoord
import Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst"
p2m_attr_erase "instance" "instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq"

noncomputable section

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing Polynomial"

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_of_ord_sub_pos {v : Place K F} {g : F} {c : K}
    (h : 0 < v.ord (g - algebraMap K F c)) : v.HasValue g c := by
  have hne : g - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt hne h.le
  have hnu : ¬ IsUnit (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    have h0' : v.ord (g - algebraMap K F c) = 0 := h0
    rw [h0'] at h
    exact lt_irrefl _ h
  have hmax : (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hres0 : residue v.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = algebraMap K v.ResidueField 0 := by
    rw [map_zero]
    exact (residue_eq_zero_iff _).mpr hmax
  have hd := hasValue_add (⟨hmem, hres0⟩ : v.HasValue (g - algebraMap K F c) 0) (v.hasValue_algebraMap c)
  rwa [sub_add_cancel, zero_add] at hd

theorem hasValue_congrRingEquiv {F' : Type*} [Field F'] [Algebra K F'] (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) (v : Place K F) {g : F} {c : K}
    (h : v.HasValue g c) : (Place.congrRingEquiv e he v).HasValue (e g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.comapSymmRingEquiv e v.toValuationSubring
  have hg' : e g ∈ (Place.congrRingEquiv e he v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨e g, hg'⟩ : (Place.congrRingEquiv e he v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c)
      = algebraMap K (Place.congrRingEquiv e he v).toValuationSubring c := by
    ext
    rw [Place.coe_comapSymmRingEquiv_apply, Place.coe_algebraMap, Place.coe_algebraMap]
    exact he c
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

theorem hasValue_placeOfPoint (a : K) (p : K[X]) :
    (RationalFunctionField.placeOfPoint K a).HasValue (algebraMap K[X] (RatFunc K) p) (p.eval a) := by
  let w := RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)
  have hmem : algebraMap K[X] (RatFunc K) p ∈ (RationalFunctionField.placeOfPoint K a).toValuationSubring :=
    RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w p
  refine ⟨hmem, ?_⟩
  have hker : p - C (p.eval a) ∈ RingHom.ker (RationalFunctionField.residueOfHeightOneSpectrum K w) := by
    rw [RationalFunctionField.ker_residueOfHeightOneSpectrum,
      RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]
    simp [IsRoot]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, RationalFunctionField.residueOfHeightOneSpectrum_apply,
    RationalFunctionField.residueOfHeightOneSpectrum_apply] at hker
  have hC : (⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :
        (RationalFunctionField.placeOfPoint K a).toValuationSubring)
      = algebraMap K (RationalFunctionField.placeOfPoint K a).toValuationSubring (p.eval a) := by
    ext
    rw [Place.coe_algebraMap, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have hker' : residue (RationalFunctionField.placeOfPoint K a).toValuationSubring ⟨_, hmem⟩
      = residue (RationalFunctionField.placeOfPoint K a).toValuationSubring
          ⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :=
    hker
  rw [hker', hC, Place.residue_algebraMap]

end PlaceLemmas

end Ws23.NodePlaceAPI

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing Polynomial ModularCurve~coeffEmb_jq"

section PlaceLemmas2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_of_hasValue' {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

end PlaceLemmas2

end Ws23.NodePlaceAPI

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq ModularCurve.NodeLocalized"

theorem qExpand_one_mul {K : Type*} [CommRing K] (q : ℕ) [NeZero q] (x : LaurentSeries K) :
    qExpand K (1 * q) x = qExpand K q x := by
  ext n
  by_cases h : (q : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have e : ((1 * q : ℕ) : ℤ) * m = (q : ℤ) * m := by rw [one_mul]
    rw [qExpand_coeff_mul]
    conv_lhs => rw [← e]
    rw [qExpand_coeff_mul]
  · have h' : ¬ ((1 * q : ℕ) : ℤ) ∣ n := by rwa [one_mul]
    rw [qExpand_coeff_of_not_dvd _ _ h', qExpand_coeff_of_not_dvd _ _ h]

theorem jqNModC_one_mul_eq_pow (K : Type*) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    jqNModC K (1 * q) = jqModC K ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [jqNModC, qExpand_one_mul, qExpand_jqModC_eq_pow_unconditional K]

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_jq (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  rw [jqNModC, ← coeffEmb_jq]
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem algebraMap_eq_single' {K : Type*} [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
    HahnSeries.ofPowerSeries_C]
  rfl

section Red

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem red_coeff_jqModC (n : ℤ) (h : (jqModC (AlgebraicClosure ℚ)).coeff n ∈ A.toSubring) :
    red ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ = (jqModC k).coeff n := by
  have hz : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ : ↥A.toSubring)
      = ((jqModC ℤ).coeff n : ↥A.toSubring) := by
    apply Subtype.ext
    show (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ↥A.toSubring) : AlgebraicClosure ℚ)
    rw [jqModC_eq_map_intCast (K := AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast, SubringClass.coe_intCast]
  rw [hz, map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff, eq_intCast]

theorem redRes_jqModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqModC k := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  exact red_coeff_jqModC red n _

theorem redRes_jqNModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqNModC k (1 * q) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  show red ⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, _⟩ = (jqNModC k (1 * q)).coeff n
  by_cases h : ((1 * q : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hm : (jqModC (AlgebraicClosure ℚ)).coeff m ∈ A.toSubring := CharPReduction.jqModC_mem_integralCoeffs A.toSubring m
    have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff ((1 * q : ℕ) * m), CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring)
        = ⟨(jqModC (AlgebraicClosure ℚ)).coeff m, hm⟩ :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff _ = _; rw [jqNModC, qExpand_coeff_mul])
    rw [hx, red_coeff_jqModC red m hm, jqNModC, qExpand_coeff_mul]
  · have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring) = 0 :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ)
                      rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl)
    rw [hx, map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem modularEval_mem_modularRing (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    modularEval N A.toSubring P ∈ CharPReduction.modularRing N A.toSubring := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact CharPReduction.constSeries_mem_modularRing N A.toSubring c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact CharPReduction.jqModC_mem_modularRing N A.toSubring
      · exact CharPReduction.jqNModC_mem_modularRing N A.toSubring

theorem redRes_modularEval [CharP k q] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by

  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).comp
      ((modularEval (1 * q) A.toSubring).codRestrict (CharPReduction.modularRing (1 * q) A.toSubring)
        (modularEval_mem_modularRing (1 * q)))
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (Polynomial.aeval (jqModC k)).toRingHom.comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    ·
      have hC : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨CharPReduction.constSeries A.toSubring c, CharPReduction.constSeries_mem_modularRing (1 * q) _ c⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_C _ _ c)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.C c))
      rw [hC, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C, algebraMap_eq_single' (red c)]
      ext n
      rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_single]
      show red ⟨(CharPReduction.constSeries A.toSubring c).coeff n, _⟩ = _
      have hcs : ∀ m : ℤ, (CharPReduction.constSeries A.toSubring c).coeff m = if m = 0 then (c : AlgebraicClosure ℚ) else 0 := by
        intro m
        show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)).coeff m = _
        rw [algebraMap_eq_single', HahnSeries.coeff_single]
        split_ifs <;> rfl
      by_cases hn : n = 0
      · subst hn
        have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff 0, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) 0⟩ : ↥A.toSubring) = c :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff 0 = c; rw [hcs, if_pos rfl])
        rw [hx, if_pos rfl]
      · have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff n, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) n⟩ : ↥A.toSubring) = 0 :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ);
                          rw [hcs, if_neg hn]; rfl)
        rw [hx, map_zero, if_neg hn]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 0)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 0))
      rw [hX, redRes_jqModC, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Polynomial.aeval_X]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 1)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 1))
      rw [hX, redRes_jqNModC, jqNModC_one_mul_eq_pow, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero,
        map_pow, Polynomial.aeval_X]
  exact RingHom.congr_fun hφψ P

omit [Fact q.Prime] in

theorem eval_graphReduce (a : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P)
      = MvPolynomial.eval₂Hom red ![a, a ^ q] P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* k :=
    (Polynomial.evalRingHom a).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφ : φ = MvPolynomial.eval₂Hom red ![a, a ^ q] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_zero, Polynomial.eval_X]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 1)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact RingHom.congr_fun hφ P

end Red

end E4b80310

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq ModularCurve.NodeLocalized"

section NodeSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem modularRedLocHom_modularEval (red : A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red
        ⟨modularEval (1 * q) A.toSubring P, CharPReduction.subring_le_localizedAtKer _ _ _ _
          (modularEval_mem_modularRing (A := A) (1 * q) P)⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by
  rw [← redRes_modularEval red P]
  exact CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
    ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (A := A) (1 * q) P⟩

end NodeSide

end E4b80310

namespace Ws23
namespace CentredSigma

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_smul_iff' (g : F) :
    σ g ∈ (σ • v).toValuationSubring ↔ g ∈ v.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

p2m_alias "P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve.Place.mem_smul_iff'" "AlgebraicCurve.Place.mem_smul_iff'"

private theorem _root_.AlgebraicCurve.Place.hasValue_smul {g : F} {c : K} (h : v.HasValue g c) :
    (σ • v).HasValue (σ g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.smulRingEquiv σ v.toValuationSubring
  have hg' : σ g ∈ (σ • v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨σ g, hg'⟩ : (σ • v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c) = algebraMap K (σ • v).toValuationSubring c := by
    ext
    rw [Place.coe_smulRingEquiv_apply, Place.coe_algebraMap, σ.commutes]
    rfl
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

p2m_alias "P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve.Place.hasValue_smul" "AlgebraicCurve.Place.hasValue_smul"

private theorem _root_.AlgebraicCurve.Place.isRational_smul (hv : v.IsRational) : (σ • v).IsRational := by
  intro z
  obtain ⟨w, hw⟩ := (Place.smulResidueAlgEquiv σ v).surjective z
  obtain ⟨c, hc⟩ := hv w
  refine ⟨c, ?_⟩
  rw [← hw, ← hc]
  exact ((Place.smulResidueAlgEquiv σ v).commutes c).symm

p2m_alias "P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve.Place.isRational_smul" "AlgebraicCurve.Place.isRational_smul"

private theorem _root_.AlgebraicCurve.Place.evalAt_smul (hv : v.IsRational) (g : F) :
    (σ • v).evalAt (σ g) = v.evalAt g := by
  by_cases hg : g ∈ v.toValuationSubring
  · have h1 : v.HasValue g (v.evalAt g) := ⟨hg, (v.algebraMap_evalAt hv hg).symm⟩
    have h2 := Place.hasValue_smul σ v h1
    rw [(σ • v).evalAt_of_mem h2.mem, h2.residue_eq, (σ • v).residueInv_algebraMap]
  · have hg' : σ g ∉ (σ • v).toValuationSubring := fun h => hg ((Place.mem_smul_iff' σ v g).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hg, dif_neg hg']

p2m_alias "P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve.Place.evalAt_smul" "AlgebraicCurve.Place.evalAt_smul"
end Generic

section Modular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

noncomputable def jE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

noncomputable def jqE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jE (q : ℕ) [Fact q.Prime] : frickeInvolutionBar (1 * q) (jE q) = jqE q := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : jE q = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]
  rfl

theorem frickeInvolutionBar_jqE (q : ℕ) [Fact q.Prime] : frickeInvolutionBar (1 * q) (jqE q) = jE q := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : jqE q = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q)) = jE q :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem frickeInvolutionBar_symm_jE (q : ℕ) [Fact q.Prime] : (frickeInvolutionBar (1 * q)).symm (jE q) = jqE q := by
  rw [AlgEquiv.symm_apply_eq]
  exact (frickeInvolutionBar_jqE q).symm

theorem frickeInvolutionBar_symm_jqE (q : ℕ) [Fact q.Prime] : (frickeInvolutionBar (1 * q)).symm (jqE q) = jE q := by
  rw [AlgEquiv.symm_apply_eq]
  exact (frickeInvolutionBar_jE q).symm

variable (red : A →+* k)

def Centred (a : k) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  (∃ x : A, red x = a ∧
      0 < W.ord (jE q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : A, red y = a ^ q ∧
      0 < W.ord (jqE q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))

theorem centred_smul {a : k} (ha2 : a ^ (q ^ 2) = a) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : Centred red a W) : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W) := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨⟨y, hya, ?_⟩, ⟨x, ?_, ?_⟩⟩
  · rw [← frickeInvolutionBar_jqE q, ← (frickeInvolutionBar (1 * q)).commutes (y : AlgebraicClosure ℚ), ← map_sub,
      Place.ord_smul]
    exact hy
  · rw [hxa, ← pow_mul, ← pow_two, ha2]
  · rw [← frickeInvolutionBar_jE q, ← (frickeInvolutionBar (1 * q)).commutes (x : AlgebraicClosure ℚ), ← map_sub,
      Place.ord_smul]
    exact hx

theorem centred_of_centred_smul {a : k} (ha2 : a ^ (q ^ 2) = a)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W)) : Centred red a W := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨⟨y, ?_, ?_⟩, ⟨x, hxa, ?_⟩⟩
  · rw [hya, ← pow_mul, ← pow_two, ha2]
  · rw [← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, frickeInvolutionBar_jE, AlgEquiv.commutes]
    exact hy
  · rw [← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, frickeInvolutionBar_jqE, AlgEquiv.commutes]
    exact hx

theorem centred_smul_iff {a : k} (ha2 : a ^ (q ^ 2) = a) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W) ↔ Centred red a W :=
  ⟨centred_of_centred_smul red ha2, centred_smul red ha2⟩

theorem forall_centred_ord_smul_eq_zero {a : k} (ha2 : a ^ (q ^ 2) = a) {f : ↥(modularFunctionFieldBar (1 * q))}
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red (a ^ q) W) :
    W.ord (frickeInvolutionBar (1 * q) f) = 0 := by
  have hW' : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • ((frickeInvolutionBar (1 * q))⁻¹ • W)) := by
    rwa [smul_inv_smul]
  have h := hford _ (centred_of_centred_smul red ha2 hW')
  rwa [← Place.ord_smul (frickeInvolutionBar (1 * q)), smul_inv_smul] at h

end Modular

end Ws23.CentredSigma

namespace Ws23
namespace SlopeLaw0

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq ModularCurve.NodeLocalized P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.NodePlaceAPI P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.CentredSigma"

section Small

set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem not_isUnit_natCast_zpow [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {n : ℤ} (hn : n ≠ 0)
    (h : ((q : AlgebraicClosure ℚ)) ^ n ∈ A) : ¬ IsUnit (⟨_, h⟩ : A) := by
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)
  have hqnu : ¬ IsUnit ((q : ℕ) : A) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqmem
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hcoe : ∀ m : ℕ, ((((q : ℕ) : A) ^ m : A) : AlgebraicClosure ℚ) = ((q : AlgebraicClosure ℚ)) ^ (m : ℤ) := by
    intro m
    rw [zpow_natCast]
    push_cast
    rfl
  intro hu
  apply hqnu
  rcases lt_or_gt_of_ne hn with hlt | hgt
  ·
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    subst hm
    have hprod : ((q : ℕ) : A) ^ (m + 1) * (⟨_, h⟩ : A) = 1 := by
      apply Subtype.ext
      show ((((q : ℕ) : A) ^ (m + 1) : A) : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ)) ^ (-((m : ℤ) + 1))
        = (1 : AlgebraicClosure ℚ)
      rw [hcoe, zpow_neg, ← Nat.cast_succ, mul_inv_cancel₀ (zpow_ne_zero _ hq0)]
    have hu2 : IsUnit (((q : ℕ) : A) ^ (m + 1)) := ⟨⟨_, _, hprod, by rwa [mul_comm] at hprod⟩, rfl⟩
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu2
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    subst hm
    have heq : (⟨_, h⟩ : A) = ((q : ℕ) : A) ^ (m + 1) := by
      apply Subtype.ext
      show ((q : AlgebraicClosure ℚ)) ^ ((m : ℤ) + 1) = (((q : ℕ) : A) ^ (m + 1) : A)
      rw [hcoe, Nat.cast_succ]
    rw [heq] at hu
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu

omit [Fact q.Prime] in

theorem pow_pow_sq_eq {a : k} (ha2 : a ^ (q ^ 2) = a) : (a ^ q) ^ (q ^ 2) = a ^ q := by
  rw [← pow_mul, mul_comm, pow_mul, ha2]

theorem pow_ne_1728 [CharP k q] {a : k} (ha2 : a ^ (q ^ 2) = a) (h1728 : a ≠ 1728) : a ^ q ≠ 1728 := by
  intro h
  apply h1728
  have h2 : (a ^ q) ^ q = (1728 : k) ^ q := by rw [h]
  rw [← pow_mul, ← pow_two, ha2] at h2
  rw [h2]
  have h3 : frobenius k q ((1728 : ℕ) : k) = ((1728 : ℕ) : k) := map_natCast (frobenius k q) 1728
  rw [frobenius_def] at h3
  exact_mod_cast h3

theorem ord_algebraMap_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0)
    {g : F} (hg : g ≠ 0) : v.ord (algebraMap K F c * g) = v.ord g := by
  rw [v.ord_mul ((map_ne_zero _).mpr hc) hg, (v.hasValue_algebraMap c).ord_eq_zero hc, zero_add]

theorem coe_algebraMap_eq_constSeries (c : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = CharPReduction.constSeries A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2⟩ := rfl

theorem algebraMap_mem_modularLocalized (red : A →+* k) (c : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [coe_algebraMap_eq_constSeries]
  exact CharPReduction.subring_le_localizedAtKer _ _ _ _
    (CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2⟩)

theorem modularRedLocHom_algebraMap [CharP k q] (red : A →+* k) (c : A)
    (h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ = algebraMap k (LaurentSeries k) (red c) := by
  have hm : modularEval (1 * q) A.toSubring (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩)
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [modularEval, MvPolynomial.eval₂Hom_C, coe_algebraMap_eq_constSeries]
  have key := E4b80310.modularRedLocHom_modularEval (q := q) (A := A) red (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩)
  rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C] at key
  have hsub : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩),
        CharPReduction.subring_le_localizedAtKer _ _ _ _
          (E4b80310.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, h⟩ := Subtype.ext hm
  rw [hsub] at key
  exact key

theorem coe_smul_eq (c : A) (g : ↥(modularFunctionFieldBar (1 * q))) :
    (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
          ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * (g : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [Algebra.smul_def]
  rfl

theorem smul_mem_modularLocalized (red : A →+* k) (c : A) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [coe_smul_eq]
  exact mul_mem (algebraMap_mem_modularLocalized red c) hg

theorem modularRedLocHom_smul [CharP k q] (red : A →+* k) (c : A) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hcg : (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hcg⟩
      = algebraMap k (LaurentSeries k) (red c) * CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ := by
  have hprod : (⟨_, hcg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, algebraMap_mem_modularLocalized red c⟩ * ⟨_, hg⟩ := Subtype.ext (coe_smul_eq c g)
  rw [hprod, map_mul, modularRedLocHom_algebraMap]

theorem nodeCoord_mem_and_evalAt_ne_zero [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red a W) :
    (jqE q - jE q ^ q) ∈ W.toValuationSubring ∧ W.evalAt (jqE q - jE q ^ q) ≠ 0 := by
  obtain ⟨c, -, ⟨d, -, hcd⟩, hV⟩ :=
    ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 W hW
  have hV' : W.HasValue (jqE q - jE q ^ q) (c : AlgebraicClosure ℚ) := hV
  refine ⟨hV'.mem, ?_⟩
  rw [evalAt_eq_of_hasValue' hV']
  intro hc0
  have hq0 : ((q : ℕ) : A) ≠ 0 := by
    intro h
    have : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by exact_mod_cast congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  apply hq0
  rw [← hcd, show c = 0 from Subtype.ext hc0, zero_mul]

theorem modularFunctionFieldC_one_mul (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    modularFunctionFieldC K (1 * q) = modularFunctionFieldC K 1 := by
  rw [modularFunctionFieldC_one, modularFunctionFieldC, E4b80310.jqNModC_one_mul_eq_pow]
  refine le_antisymm ?_ (IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  · exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton (jqModC K))) q

theorem modularRedLocHom_mem_one [CharP k q] (red : A →+* k)
    (g : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red g ∈ modularFunctionFieldC k 1 := by
  rw [← modularFunctionFieldC_one_mul k q]
  exact CharPReduction.modularRedLocHom_mem A.toSubring red (1 * q) g

end Small

end Ws23.SlopeLaw0

namespace Ws23
namespace TwoBranchCore

p2m_open "IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve ModularCurve~coeffEmb_jq ModularCurve.CharPReduction"

section GaussUnits

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] {A : Subring L} {k : Type*} [Field k] {red : A →+* k}

theorem gaussUnit_mul {f g : LaurentSeries L}
    (hf : ∃ h : f ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f, h⟩ ≠ 0)
    (hg : ∃ h : g ∈ modularLocalized N A red, modularRedLocHom N A red ⟨g, h⟩ ≠ 0) :
    ∃ h : f * g ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f * g, h⟩ ≠ 0 := by
  obtain ⟨hf, hfu⟩ := hf
  obtain ⟨hg, hgu⟩ := hg
  refine ⟨mul_mem hf hg, ?_⟩
  have : (⟨f * g, mul_mem hf hg⟩ : modularLocalized N A red) = ⟨f, hf⟩ * ⟨g, hg⟩ := rfl
  rw [this, map_mul]
  exact mul_ne_zero hfu hgu

theorem redRes_num_ne_zero {f : LaurentSeries L} (hf : f ∈ modularLocalized N A red)
    (hfu : modularRedLocHom N A red ⟨f, hf⟩ ≠ 0) {r s : modularRing N A}
    (hs : s ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A))
    (hfs : f * s = r) :
    redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r ≠ 0 := by
  have hspec : redLoc (⟨f, hf⟩ : modularLocalized N A red) *
      redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) s
        = redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r :=
    redLoc_spec (A := A) (red := red) (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A)
      ⟨f, hf⟩ hfs
  have hfu' : redLoc (⟨f, hf⟩ : modularLocalized N A red) ≠ 0 := hfu
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) hs
  rw [← hspec]; exact mul_ne_zero hfu' hsne

theorem gaussUnit_inv {f : LaurentSeries L}
    (hf : ∃ h : f ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f, h⟩ ≠ 0) :
    ∃ h : f⁻¹ ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f⁻¹, h⟩ ≠ 0 := by
  obtain ⟨hf, hfu⟩ := hf
  have hf' := hf
  rw [modularLocalized, mem_localizedAtKer] at hf'
  obtain ⟨r, s, hs, hfs⟩ := hf'
  have hrne := redRes_num_ne_zero hf hfu hs hfs
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) hs
  have hr : r ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) :=
    (notMem_redKer_iff A red _ _).mpr hrne
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hrne
    rw [zero_mul] at hfs
    have : r = 0 := Subtype.ext hfs.symm
    rw [this, map_zero]
  have hpres : f⁻¹ * r = s := by
    rw [← hfs, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
  have hinvmem : f⁻¹ ∈ modularLocalized N A red := by
    rw [modularLocalized, mem_localizedAtKer]
    exact ⟨s, r, hr, hpres⟩
  refine ⟨hinvmem, ?_⟩
  have hspec' : redLoc (⟨f⁻¹, hinvmem⟩ : modularLocalized N A red) *
      redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r
        = redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) s :=
    redLoc_spec (A := A) (red := red) (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A)
      ⟨f⁻¹, hinvmem⟩ hpres
  intro h0
  apply hsne
  have h0' : redLoc (⟨f⁻¹, hinvmem⟩ : modularLocalized N A red) = 0 := h0
  rw [← hspec', h0', zero_mul]

theorem gaussUnit_zpow {f : LaurentSeries L}
    (hf : ∃ h : f ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f, h⟩ ≠ 0) (m : ℤ) :
    ∃ h : f ^ m ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f ^ m, h⟩ ≠ 0 := by
  have hnat : ∀ n : ℕ, ∃ h : f ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f ^ n, h⟩ ≠ 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [pow_zero]; exact one_mem _, ?_⟩
      have : (⟨f ^ 0, by rw [pow_zero]; exact one_mem _⟩ : modularLocalized N A red) = 1 :=
        Subtype.ext (pow_zero f)
      rw [this, map_one]; exact one_ne_zero
    | succ n ih =>
      have := gaussUnit_mul ih hf
      rwa [← pow_succ] at this
  rcases m with n | n
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hnat n
  · have := gaussUnit_inv (hnat (n + 1))
    simpa only [zpow_negSucc] using this

theorem ne_zero_of_gaussUnit {f : LaurentSeries L}
    (hf : ∃ h : f ∈ modularLocalized N A red, modularRedLocHom N A red ⟨f, h⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  obtain ⟨h, hu⟩ := hf
  apply hu
  have : (⟨0, h⟩ : modularLocalized N A red) = 0 := rfl
  rw [this, map_zero]

theorem exists_coeff_red_ne_zero (t : modularRing N A)
    (ht : redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) t ≠ 0) :
    ∃ n : ℤ, red ⟨(t : LaurentSeries L).coeff n, modularRing_le_integralCoeffs N A t.2 n⟩ ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply ht
  ext n
  rw [redRes_apply, coeffRed_coeff]
  simpa using hall n

end GaussUnits

section Constants

theorem coeff_algebraMap_mul {L : Type*} [Field L] (c : L) (x : LaurentSeries L) (n : ℤ) :
    (algebraMap L (LaurentSeries L) c * x).coeff n = c * x.coeff n := by
  have h : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
    ext m
    rw [HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) c = PowerSeries.C c from by simp,
      HahnSeries.ofPowerSeries_C]
  rw [h, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] {A : ValuationSubring L} {k : Type*} [Field k]

theorem gaussUnit_congr {red : A →+* k} {f g : LaurentSeries L} (e : f = g)
    (hf : ∃ h : f ∈ modularLocalized N A.toSubring red, modularRedLocHom N A.toSubring red ⟨f, h⟩ ≠ 0) :
    ∃ h : g ∈ modularLocalized N A.toSubring red, modularRedLocHom N A.toSubring red ⟨g, h⟩ ≠ 0 := by
  subst e; exact hf

theorem inv_mem_of_red_ne_zero (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {u : L} (hu : u ∈ A) (hru : red ⟨u, hu⟩ ≠ 0) : u ≠ 0 ∧ u⁻¹ ∈ A := by
  have hunit : IsUnit (⟨u, hu⟩ : A) := by
    by_contra hnu
    exact hru ((hker _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  obtain ⟨w, hw⟩ := hunit
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hru
    have : (⟨(0 : L), hu⟩ : A) = 0 := rfl
    rw [this, map_zero]
  refine ⟨hu0, ?_⟩
  have hmul : ((w : A) : L) * ((w⁻¹ : Aˣ) : A) = 1 := congrArg Subtype.val (Units.mul_inv w)
  rw [hw] at hmul
  have : u⁻¹ = ((w⁻¹ : Aˣ) : A) := (eq_inv_of_mul_eq_one_right hmul).symm
  rw [this]
  exact ((w⁻¹ : Aˣ) : A).2

theorem const_mem_of_gaussUnit_algebraMap (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {c : L}
    (h : ∃ h : algebraMap L (LaurentSeries L) c ∈ modularLocalized N A.toSubring red,
      modularRedLocHom N A.toSubring red ⟨_, h⟩ ≠ 0) :
    c ∈ A ∧ c⁻¹ ∈ A := by
  obtain ⟨hm, hu⟩ := h
  have hm' := hm
  rw [modularLocalized, mem_localizedAtKer] at hm'
  obtain ⟨r, s, hs, hcs⟩ := hm'
  have hrne := redRes_num_ne_zero hm hu hs hcs
  have hsne := redRes_ne_zero_of_notMem (A := A.toSubring) (red := red) (R := modularRing N A.toSubring)
    (hR := modularRing_le_integralCoeffs N A.toSubring) hs
  have hcoeff : ∀ n : ℤ, c * (s : LaurentSeries L).coeff n = (r : LaurentSeries L).coeff n := by
    intro n
    have e := congrArg (fun x : LaurentSeries L => x.coeff n) hcs
    beta_reduce at e
    rw [← e, coeff_algebraMap_mul]
  obtain ⟨n, hn⟩ := exists_coeff_red_ne_zero s hsne
  obtain ⟨hsn0, hsninv⟩ := inv_mem_of_red_ne_zero red hker (modularRing_le_integralCoeffs N A.toSubring s.2 n) hn
  have hcA : c ∈ A := by
    have ec : c = (r : LaurentSeries L).coeff n * ((s : LaurentSeries L).coeff n)⁻¹ := by
      rw [← hcoeff n, mul_assoc, mul_inv_cancel₀ hsn0, mul_one]
    rw [ec]
    exact mul_mem (modularRing_le_integralCoeffs N A.toSubring r.2 n) hsninv
  obtain ⟨n', hn'⟩ := exists_coeff_red_ne_zero r hrne
  obtain ⟨hrn0, hrninv⟩ := inv_mem_of_red_ne_zero red hker (modularRing_le_integralCoeffs N A.toSubring r.2 n') hn'
  have hcinv : c⁻¹ = (s : LaurentSeries L).coeff n' * ((r : LaurentSeries L).coeff n')⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hcoeff n', mul_inv_cancel₀ hrn0]
  refine ⟨hcA, ?_⟩
  rw [hcinv]
  exact mul_mem (modularRing_le_integralCoeffs N A.toSubring s.2 n') hrninv

end Constants

section ConstUnit

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem isUnit_const_of_gaussUnit_smul (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (g : ↥(modularFunctionFieldBar N)) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (hg : ((g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized N A.toSubring red)
    (hgu : modularRedLocHom N A.toSubring red ⟨_, hg⟩ ≠ 0)
    (hcg : ((c • g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized N A.toSubring red)
    (hcgu : modularRedLocHom N A.toSubring red ⟨_, hcg⟩ ≠ 0) :
    ∃ h : c ∈ A, IsUnit (⟨c, h⟩ : A) := by
  have hg0 : ((g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    ne_zero_of_gaussUnit ⟨hg, hgu⟩
  have ecoe : ((c • g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c
        * ((g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [IntermediateField.coe_smul, Algebra.smul_def]
  have e : ((c • g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
        * (((g : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)))⁻¹
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c := by
    rw [ecoe, mul_assoc, mul_inv_cancel₀ hg0, mul_one]
  have hconst := gaussUnit_congr e (gaussUnit_mul ⟨hcg, hcgu⟩ (gaussUnit_inv ⟨hg, hgu⟩))
  obtain ⟨hcA, hcinvA⟩ := const_mem_of_gaussUnit_algebraMap red hker hconst
  exact ⟨hcA, ⟨⟨⟨c, hcA⟩, ⟨c⁻¹, hcinvA⟩, Subtype.ext (mul_inv_cancel₀ hc), Subtype.ext (inv_mul_cancel₀ hc)⟩, rfl⟩⟩

theorem inv_mem_of_isUnit {L : Type*} [Field L] {A : ValuationSubring L} {c : L} (hcA : c ∈ A)
    (hu : IsUnit (⟨c, hcA⟩ : A)) : c⁻¹ ∈ A := by
  obtain ⟨w, hw⟩ := hu
  have hmul : ((w : A) : L) * ((w⁻¹ : Aˣ) : A) = 1 := congrArg Subtype.val (Units.mul_inv w)
  rw [hw] at hmul
  have : c⁻¹ = ((w⁻¹ : Aˣ) : A) := inv_eq_of_mul_eq_one_right hmul
  rw [this]
  exact ((w⁻¹ : Aˣ) : A).2

end ConstUnit

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have hle : v.adicValuation f ≤ 1 := v.adicValuation_le_one_of_mem hf
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  simp only [Place.ord]
  omega

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  rcases (ord_nonneg_of_mem v hf).eq_or_lt with h0 | hpos
  · exact h0.symm
  · exfalso
    apply h
    rw [v.evalAt_of_mem hf]
    have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h0 := v.ord_coe_unit u
      rw [hu] at h0
      simp only at h0
      omega
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    rw [hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem evalAt_inv (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, neg_zero]
  have hmul := v.evalAt_mul_of_mem hv (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge)
    (v.mem_toValuationSubring_of_ord_nonneg_alt hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem evalAt_zpow (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  have hpow : ∀ m : ℕ, v.evalAt (f ^ m) = v.evalAt f ^ m := by
    intro m
    induction m with
    | zero => simp [v.evalAt_one]
    | succ m ih =>
      have hm : v.ord (f ^ (m : ℤ)) = 0 := by rw [v.ord_zpow, h, mul_zero]
      rw [pow_succ, v.evalAt_mul_of_mem hv ?_ (v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge), ih,
        pow_succ]
      have : (f ^ m : F) = f ^ (m : ℤ) := by rw [zpow_natCast]
      rw [this]
      exact v.mem_toValuationSubring_of_ord_nonneg_alt (zpow_ne_zero _ hf) hm.ge
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc, zpow_negSucc, ← hpow (m + 1)]
    refine evalAt_inv v hv (pow_ne_zero _ hf) ?_
    have : (f ^ (m + 1) : F) = f ^ ((m + 1 : ℕ) : ℤ) := by rw [zpow_natCast]
    rw [this, v.ord_zpow, h, mul_zero]

private theorem _root_.Ws23.TwoBranchCore.evalAt_smul (v : Place K F) (hv : v.IsRational) (c : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' c) hf, v.evalAt_algebraMap_eq]

p2m_export "Ws23.TwoBranchCore" "evalAt_smul"

theorem isRational_of_deg_eq_one (v : Place K F) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra K v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra K v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

theorem isRational_modularFunctionFieldBar (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : w.IsRational :=
  isRational_of_deg_eq_one w (ModularCurve.deg_eq_one_modularFunctionFieldBar M w)

end PlaceHelpers

section Core

set_option maxHeartbeats 1600000 in

theorem isUnit_evalAt_smul_mul_zpow_of_twoBranch
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q))) (c : AlgebraicClosure ℚ) (hc0 : c ≠ 0) (m : ℤ)
    (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) :
        modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ h : W.evalAt (c • f) * W.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
                modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)⁻¹) ^ m ∈ A, IsUnit (⟨_, h⟩ : A) := by
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  obtain ⟨G, hG⟩ : ∃ G : ↥(modularFunctionFieldBar (1 * q)), G = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
                modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ↥(modularFunctionFieldBar (1 * q)), z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹ :=
    ⟨_, rfl⟩
  rw [← hG, ← hz]

  obtain ⟨hz1, hσG⟩ := ModularCurve.NodeLocalized.gaussData_nodeCoord red hq a ha h0 h1728
  rw [← hG] at hz1 hσG
  rw [← hz] at hz1
  have hG0 : G ≠ 0 := by
    intro h
    apply ne_zero_of_gaussUnit hσG
    rw [h, map_zero]; rfl
  have hz0 : z ≠ 0 := by
    rw [hz]; exact mul_ne_zero ((map_ne_zero _).mpr hq0) (inv_ne_zero hG0)
  have hGval : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
      G ∈ V.toValuationSubring ∧ V.ord G = 0 := by
    intro V hV
    obtain ⟨cV, -, ⟨d, -, hcd⟩, hGc⟩ :=
      ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 V hV
    rw [← hG] at hGc
    have hrat : V.IsRational := isRational_modularFunctionFieldBar (1 * q) V
    have hcV0 : (cV : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0c
      apply hq0
      have := congrArg (fun x : ↥A => (x : AlgebraicClosure ℚ)) hcd
      beta_reduce at this
      push_cast at this
      rw [← this, h0c, zero_mul]
    have hev : V.evalAt G = (cV : AlgebraicClosure ℚ) := by
      obtain ⟨hm, hres⟩ := hGc
      have h1 := V.algebraMap_evalAt hrat hm
      exact (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective (h1.trans hres)
    refine ⟨hGc.1, ord_eq_zero_of_evalAt_ne_zero V hGc.1 ?_⟩
    rw [hev]; exact hcV0
  have hzord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → V.ord z = 0 := by
    intro V hV
    rw [hz, Place.ord_mul _ ((map_ne_zero _).mpr hq0) (inv_ne_zero hG0), ConstantReduction.ord_algebraMap V hq0,
      Place.ord_inv, (hGval V hV).2, neg_zero, add_zero]
  have hcf0 : (c • f : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h
    apply ne_zero_of_gaussUnit ⟨h₁, h₁u⟩
    rw [h]; rfl
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hcf0 (smul_zero c)

  have hH1 : ∃ h : (((c • f) * z ^ m : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 :=
    gaussUnit_mul ⟨h₁, h₁u⟩ (gaussUnit_zpow hz1 m)

  have esf : (c • f : ↥(modularFunctionFieldBar (1 * q))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c * f := Algebra.smul_def c f
  have es1 : ((c * (q : AlgebraicClosure ℚ) ^ m) • f : ↥(modularFunctionFieldBar (1 * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f := Algebra.smul_def _ f
  have eH : ((c * (q : AlgebraicClosure ℚ) ^ m) • f : ↥(modularFunctionFieldBar (1 * q))) * G ^ (-m) = (c • f) * z ^ m := by
    rw [es1, esf, hz, mul_zpow, map_mul, map_zpow₀, inv_zpow']
    ring
  have eσ : frickeInvolutionBar (1 * q) ((c • f) * z ^ m)
      = frickeInvolutionBar (1 * q) ((c * (q : AlgebraicClosure ℚ) ^ m) • f : ↥(modularFunctionFieldBar (1 * q)))
        * (frickeInvolutionBar (1 * q) G) ^ (-m) := by
    rw [← eH, map_mul, map_zpow₀]
  have keyσ : ∀ (y : ↥(modularFunctionFieldBar (1 * q))), y = frickeInvolutionBar (1 * q) ((c * (q : AlgebraicClosure ℚ) ^ m) • f : ↥(modularFunctionFieldBar (1 * q)))
        * (frickeInvolutionBar (1 * q) G) ^ (-m) →
      ∃ h : ((y : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    intro y e
    subst e
    exact gaussUnit_mul ⟨h₂, h₂u⟩ (gaussUnit_zpow hσG (-m))
  obtain ⟨hH1m, hH1u⟩ := hH1
  obtain ⟨hH2m, hH2u⟩ := keyσ _ eσ
  have hHord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → V.ord ((c • f) * z ^ m) = 0 := by
    intro V hV
    rw [Place.ord_mul _ hcf0 (zpow_ne_zero m hz0), ConstantReduction.ord_smul V hc0 f, hford V hV,
      Place.ord_zpow, hzord V hV, mul_zero, add_zero]

  have hmax :=
    ModularCurve.NodeLocalized.isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
      red hker hq a ha ha2 h0 h1728 ((c • f) * z ^ m) hH1m hH1u hH2m hH2u hHord W hW

  have hrat : W.IsRational := isRational_modularFunctionFieldBar (1 * q) W
  have hfW : f ∈ W.toValuationSubring := W.mem_toValuationSubring_of_ord_nonneg_alt hf0 (hford W hW).ge
  have hcfW : (c • f : ↥(modularFunctionFieldBar (1 * q))) ∈ W.toValuationSubring := by
    rw [esf]; exact mul_mem (W.algebraMap_mem' c) hfW
  have hzmW : z ^ m ∈ W.toValuationSubring :=
    W.mem_toValuationSubring_of_ord_nonneg_alt (zpow_ne_zero m hz0) (by rw [Place.ord_zpow, hzord W hW, mul_zero])
  have e : W.evalAt ((c • f) * z ^ m) = W.evalAt (c • f) * W.evalAt z ^ m := by
    rw [W.evalAt_mul_of_mem hrat hcfW hzmW, evalAt_zpow W hrat hz0 (hzord W hW)]
  rw [e] at hmax
  exact hmax

end Core

end TwoBranchCore
end Ws23

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Place.deg Place.ord Place.ord_zero Place.ord_mul Place.ord_inv Place.ord_zpow Place.smulRingEquiv Place.coe_smulRingEquiv_apply Place.smul_toValuationSubring Place.ord_smul Place.smulResidueAlgEquiv Place.residue_algebraMap GluedPic0 RationalFunctionField.heightOneSpectrumOfIrreducible RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum_apply RationalFunctionField.ker_residueOfHeightOneSpectrum RationalFunctionField.placeOfPoint Place.comapSymmRingEquiv Place.coe_comapSymmRingEquiv_apply Place.congrRingEquiv Place.evalAt ComponentChart Annulus ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place.mem_smul_iff' Place.hasValue_smul Place.isRational_smul Place.evalAt_smul"
p2m_open "AlgebraicCurve"
namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue residue_algebraMap ker_residue dom"
p2m_open "AlgebraicCurve.ComponentChart"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero (C : ComponentChart A F Fbar) {g : F} (hg : g ∈ C.integers)
    (h : C.residue ⟨g, hg⟩ ≠ 0) : IsUnit (⟨g, hg⟩ : C.integers) := by
  by_contra hnu
  apply h
  have hmem : (⟨g, hg⟩ : C.integers) ∈ maximalIdeal C.integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
  rw [← C.ker_residue] at hmem
  exact hmem

p2m_export "AlgebraicCurve.ComponentChart" "isUnit_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.inv_mem_of_residue_ne_zero (C : ComponentChart A F Fbar) {g : F} (hg : g ∈ C.integers)
    (h : C.residue ⟨g, hg⟩ ≠ 0) : g⁻¹ ∈ C.integers := by
  obtain ⟨u, hu⟩ := C.isUnit_of_residue_ne_zero hg h
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply h
    have : (⟨0, hg⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have hmul : ((u : C.integers) : F) * ((u⁻¹ : C.integersˣ) : C.integers) = 1 := by
    have h1 : (u : C.integers) * ((u⁻¹ : C.integersˣ) : C.integers) = 1 := Units.mul_inv u
    exact congrArg Subtype.val h1
  have hginv : g⁻¹ = ((u⁻¹ : C.integersˣ) : C.integers) := by
    rw [hu] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  rw [hginv]
  exact ((u⁻¹ : C.integersˣ) : C.integers).2

p2m_export "AlgebraicCurve.ComponentChart" "inv_mem_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.const_mem_of_smul_unit (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers)
    (hfres : C.residue ⟨f, hf⟩ ≠ 0) {c : L} (hcf : c • f ∈ C.integers)
    (hcfres : C.residue ⟨c • f, hcf⟩ ≠ 0) : c ∈ A ∧ c⁻¹ ∈ A := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hfres
    have : (⟨0, hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have hfinv : f⁻¹ ∈ C.integers := C.inv_mem_of_residue_ne_zero hf hfres
  have hginv : (c • f)⁻¹ ∈ C.integers := C.inv_mem_of_residue_ne_zero hcf hcfres
  have hcF : algebraMap L F c = (c • f) * f⁻¹ := by
    rw [Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hf0, mul_one]
  have hcinvF : algebraMap L F c⁻¹ = f * (c • f)⁻¹ := by
    rw [Algebra.smul_def, mul_inv, map_inv₀, ← mul_assoc, mul_comm f, mul_assoc, mul_inv_cancel₀ hf0,
      mul_one]
  constructor
  · rw [← C.algebraMap_mem_iff, hcF]; exact mul_mem hcf hfinv
  · rw [← C.algebraMap_mem_iff, hcinvF]; exact mul_mem hf hginv

p2m_export "AlgebraicCurve.ComponentChart" "const_mem_of_smul_unit"

private theorem _root_.AlgebraicCurve.ComponentChart.ord_residue_smul_eq (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    {f : F} (hf : f ∈ C.integers) {c : L} (hcA : c ∈ A) (hcu : IsUnit (⟨c, hcA⟩ : A))
    (hcf : c • f ∈ C.integers) :
    x.ord (C.residue ⟨c • f, hcf⟩) = x.ord (C.residue ⟨f, hf⟩) := by
  have hcres : C.residue ⟨algebraMap L F c, (C.algebraMap_mem_iff c).mpr hcA⟩
      = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨c, hcA⟩) :=
    C.residue_algebraMap ⟨c, hcA⟩
  have hcres0 : algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨c, hcA⟩) ≠ 0 := by
    rw [map_ne_zero]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hcu
  have hsplit : (⟨c • f, hcf⟩ : C.integers)
      = ⟨algebraMap L F c, (C.algebraMap_mem_iff c).mpr hcA⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def c f)
  rw [hsplit, map_mul, hcres]
  by_cases hfr : C.residue ⟨f, hf⟩ = 0
  · rw [hfr, mul_zero]
  · rw [Place.ord_mul _ hcres0 hfr,
      ConstantReduction.ord_algebraMap x ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hcu), zero_add]

p2m_export "AlgebraicCurve.ComponentChart" "ord_residue_smul_eq"
end ComponentChart
end AlgebraicCurve

set_option synthInstance.maxHeartbeats 80000

namespace Ws23
namespace SlopeLaw0

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq ModularCurve.NodeLocalized P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.NodePlaceAPI P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.CentredSigma P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.TwoBranchCore"

section Core

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

def UnitA (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) : Prop := ∃ h : x ∈ A, IsUnit (⟨x, h⟩ : A)

omit [Fact q.Prime] in
theorem UnitA.mul {x y : AlgebraicClosure ℚ} (hx : UnitA A x) (hy : UnitA A y) : UnitA A (x * y) := by
  obtain ⟨hx, hxu⟩ := hx
  obtain ⟨hy, hyu⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : A) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this]
  exact hxu.mul hyu

omit [Fact q.Prime] in
theorem UnitA.ne_zero {x : AlgebraicClosure ℚ} (hx : UnitA A x) : x ≠ 0 := by
  obtain ⟨hx, hxu⟩ := hx
  intro h0
  apply hxu.ne_zero
  exact Subtype.ext h0

omit [Fact q.Prime] in
theorem UnitA.inv {x : AlgebraicClosure ℚ} (hx : UnitA A x) : UnitA A x⁻¹ := by
  obtain ⟨hx, u, hu⟩ := hx
  have h1 : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = x⁻¹ := by
    have h3 : x * (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
      have h4 : ((u : A) : AlgebraicClosure ℚ) = x := by rw [hu]
      rw [← h4, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]
      rfl
    exact eq_inv_of_mul_eq_one_right h3
  have hmem : x⁻¹ ∈ A := by rw [← h1]; exact ((u⁻¹ : Aˣ) : A).2
  refine ⟨hmem, ?_⟩
  have : (⟨x⁻¹, hmem⟩ : A) = ((u⁻¹ : Aˣ) : A) := Subtype.ext h1.symm
  rw [this]
  exact Units.isUnit _

omit [Fact q.Prime] in

theorem UnitA.of_mul_left {x y : AlgebraicClosure ℚ} (hxy : UnitA A (x * y)) (hx : UnitA A x) : UnitA A y := by
  have h := (hx.inv).mul hxy
  rwa [← mul_assoc, inv_mul_cancel₀ hx.ne_zero, one_mul] at h

omit [Fact q.Prime] in
theorem UnitA.congr {x y : AlgebraicClosure ℚ} (hx : UnitA A x) (e : x = y) : UnitA A y := e ▸ hx

theorem UnitA.red_ne_zero (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {x : AlgebraicClosure ℚ} (hx : UnitA A x) : red ⟨x, hx.1⟩ ≠ 0 := by
  obtain ⟨hmem, hu⟩ := hx
  intro h
  have := (hker _).mp h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
  exact this hu

theorem eq_zero_of_unitA_natCast_zpow [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {n : ℤ}
    (h : UnitA A (((q : AlgebraicClosure ℚ)) ^ n)) : n = 0 := by
  by_contra hn
  obtain ⟨hmem, hu⟩ := h
  exact not_isUnit_natCast_zpow red hker hn hmem hu

theorem frickeInvolutionBar_smul (c : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) :
    frickeInvolutionBar (1 * q) (c • x) = c • frickeInvolutionBar (1 * q) x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

theorem isRational_W (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : W.IsRational := by
  intro z
  have h : W.deg = 1 := deg_eq_one_modularFunctionFieldBar (1 * q) W
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra (AlgebraicClosure ℚ) W.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra (AlgebraicClosure ℚ) W.ResidueField) := by rw [hbt]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

variable [CharP k q] [IsAlgClosed k] [DecidableEq k]

theorem exists_zeroChart_slopeData (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0) :
    ∃ (d : AlgebraicClosure ℚ) (m : ℤ)
      (h₂ : ((frickeInvolutionBar (1 * q) ((d • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1),
      d ≠ 0 ∧ CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 ∧
      (charLGeomPlaceOfPoint k (a ^ q)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC k 1)) = m ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        UnitA A (d * W.evalAt f * W.evalAt (jqE q - jE q ^ q) ^ (-m)) := by
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  haveI : PerfectField k := IsAlgClosed.perfectField k

  obtain ⟨c, hc0, m, h₁, h₂', h₁u, h₂u'⟩ :=
    ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero
      red hker hq a ha ha2 h0 h1728 f hf (fun W h => hford W h)
  set d : AlgebraicClosure ℚ := c * (q : AlgebraicClosure ℚ) ^ m with hd
  have hd0 : d ≠ 0 := mul_ne_zero hc0 (zpow_ne_zero _ hq0)
  have h₂F := modularRedLocHom_mem_one red ⟨_, h₂'⟩
  refine ⟨d, m, h₂', h₂F, hd0, h₂u', ?_, ?_⟩
  ·
    set g : ↥(modularFunctionFieldBar (1 * q)) := frickeInvolutionBar (1 * q) (d • f) with hg
    have hb : a ^ q ∈ ssJSet q k := (pow_mem_ssJSet_iff_of_perfectField q a).mpr ha
    have hdf0 : (d • f : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := smul_ne_zero hd0 hf
    have hg0 : g ≠ 0 := (map_ne_zero_iff _ (frickeInvolutionBar (1 * q)).injective).mpr hdf0

    have hford_df : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        W.ord (d • f : ↥(modularFunctionFieldBar (1 * q))) = 0 := by
      intro W hW
      rw [Algebra.smul_def, ord_algebraMap_mul W hd0 hf]
      exact hford W hW
    obtain ⟨c', hc'0, m', h₁', h₂'', h₁F', h₁u', h₂u'', hord'⟩ :=
      ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
        red hker hq (a ^ q) hb (pow_pow_sq_eq ha2) (pow_ne_zero _ h0) (pow_ne_1728 ha2 h1728)
        g hg0 (fun W h => forall_centred_ord_smul_eq_zero red ha2 hford_df W h)

    have huc' : UnitA A c' := isUnit_const_of_gaussUnit_smul red hker g c' hc'0 h₂' h₂u' h₁' h₁u'

    set e : AlgebraicClosure ℚ := c' * (q : AlgebraicClosure ℚ) ^ m' with he
    have e2 : frickeInvolutionBar (1 * q) ((e • g : modularFunctionFieldBar (1 * q)))
        = (e * d / c) • (c • f) := by
      rw [hg, frickeInvolutionBar_smul, frickeInvolutionBar_frickeInvolutionBar, smul_smul, smul_smul,
        div_mul_cancel₀ _ hc0]
    have hdg : ((((e * d / c) • (c • f) : ↥(modularFunctionFieldBar (1 * q)))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [← e2]; exact h₂''
    have hdgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hdg⟩ ≠ 0 := by
      have : (⟨_, hdg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, h₂''⟩ :=
        Subtype.ext (congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) e2.symm)
      rw [this]; exact h₂u''
    have hued : UnitA A (e * d / c) :=
      isUnit_const_of_gaussUnit_smul red hker (c • f) (e * d / c)
        (div_ne_zero (mul_ne_zero (mul_ne_zero hc'0 (zpow_ne_zero _ hq0)) hd0) hc0) h₁ h₁u hdg hdgu

    have hqpow : UnitA A (((q : AlgebraicClosure ℚ)) ^ (m + m')) := by
      refine UnitA.congr (hued.mul huc'.inv) ?_
      rw [he, hd, zpow_add₀ hq0]
      field_simp
    have hmm' : m' = -m := by
      have := eq_zero_of_unitA_natCast_zpow red hker hqpow
      omega

    have hc'A : c' ∈ A := huc'.1
    have hred' : red ⟨c', hc'A⟩ ≠ 0 := huc'.red_ne_zero red hker
    have hscal : (⟨_, h₁F'⟩ : ↥(modularFunctionFieldC k 1))
        = algebraMap k (modularFunctionFieldC k 1) (red ⟨c', hc'A⟩) * ⟨_, h₂F⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul]
      exact modularRedLocHom_smul red ⟨c', hc'A⟩ h₂' h₁'
    have hx0 : (⟨_, h₂F⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := fun h => h₂u' (congrArg Subtype.val h)
    have h5 := hord'
    rw [frobNodePair_fst, hscal, ord_algebraMap_mul _ hred' hx0] at h5
    rw [h5, hmm', neg_neg]
  ·
    intro W hW
    have hWrat : W.IsRational := isRational_W W
    obtain ⟨hmemU, huU⟩ := isUnit_evalAt_smul_mul_zpow_of_twoBranch red hker hq a ha ha2 h0 h1728 f c hc0 m h₁ h₁u h₂' h₂u'
      (fun W h => hford W h) W hW
    obtain ⟨hGmem, hGne⟩ := nodeCoord_mem_and_evalAt_ne_zero red hker hq a ha ha2 h0 h1728 W hW
    set G : ↥(modularFunctionFieldBar (1 * q)) := jqE q - jE q ^ q with hGdef
    set γ : AlgebraicClosure ℚ := W.evalAt G with hγ
    have hGval : W.HasValue G γ := ⟨hGmem, (W.algebraMap_evalAt hWrat hGmem).symm⟩
    have hzval : W.HasValue (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹)
        ((q : AlgebraicClosure ℚ) * γ⁻¹) := (W.hasValue_algebraMap _).mul (hGval.inv hGne)
    have hz : W.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹)
        = (q : AlgebraicClosure ℚ) * γ⁻¹ := evalAt_eq_of_hasValue' hzval
    have hfmem : f ∈ W.toValuationSubring := W.mem_toValuationSubring_of_ord_nonneg_alt hf (hford W hW).ge
    have hcf : W.evalAt (c • f) = c * W.evalAt f := by
      rw [Algebra.smul_def, W.evalAt_mul_of_mem hWrat (W.algebraMap_mem' c) hfmem, W.evalAt_algebraMap_eq]
    refine UnitA.congr ⟨hmemU, huU⟩ ?_
    show W.evalAt (c • f) * W.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m = _
    rw [hcf, hz, mul_zpow, inv_zpow', hd]
    ring

end Core

end Ws23.SlopeLaw0

namespace Ws23
namespace SlopeLaw0
p2m_open "IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.AlgebraicCurve ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ.Ws23.CentredSigma"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem slopeLaw_ssAnnulus_zeroChart_aux (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p) (n : ℕ) [NeZero n] (hn : n = 1 * p)
    {Fbar0 : Type*} [Field Fbar0] [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar n) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An : Annulus A ↥(modularFunctionFieldBar n))
    (hparam : An.param = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full n (dvd_refl n))⟩ :
                modularFunctionFieldBar n)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full n (jq_mem n))⟩ : modularFunctionFieldBar n) ^ p))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar n), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full n (jq_mem n))⟩ : modularFunctionFieldBar n)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar n) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full n (dvd_refl n))⟩ :
                modularFunctionFieldBar n)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar n) (y : AlgebraicClosure ℚ)))))
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar n))
        (h₂ : ((frickeInvolutionBar n g : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar n)) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar n g : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar n)) (hf : f ∈ C0.integers), C0.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x0.ord (C0.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  subst hn
  intro f hf hfres hford P hP
  have hker : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hfres
    have : (⟨0, hf⟩ : C0.integers) = 0 := rfl
    rw [this, map_zero]

  obtain ⟨d, m, h₂, h₂F, hd0, h₂u, hord, hunitW⟩ :=
    exists_zeroChart_slopeData (IsLocalRing.residue ↥A) hker hp5 a ha ha2 h0 h1728 f hf0
      (fun W hW => hford W ((hdom W).mpr hW))

  obtain ⟨hgC, hgres⟩ := hunit0 (d • f) h₂ h₂u
  obtain ⟨hdA, hdinvA⟩ := C0.const_mem_of_smul_unit hf hfres hgC hgres
  have hdunit : IsUnit (⟨d, hdA⟩ : ↥A) :=
    ⟨⟨⟨d, hdA⟩, ⟨d⁻¹, hdinvA⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  have hn : x0.ord (C0.residue ⟨f, hf⟩) = m := by
    rw [← C0.ord_residue_smul_eq x0 hf hdA hdunit hgC, hordres0 (d • f) hgC h₂ h₂F]
    exact hord
  rw [hn, hparam]
  show ∃ h : P.evalAt f * P.evalAt (jqE p - jE p ^ p) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : ↥A)

  obtain ⟨hmem, hu⟩ := hunitW P ((hdom P).mp hP)
  have hquot : P.evalAt f * P.evalAt (jqE p - jE p ^ p) ^ (-m) = d⁻¹ * (d * P.evalAt f * P.evalAt (jqE p - jE p ^ p) ^ (-m)) := by
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul (P.evalAt f)]
  have hmemA : P.evalAt f * P.evalAt (jqE p - jE p ^ p) ^ (-m) ∈ A := by
    rw [hquot]; exact mul_mem hdinvA hmem
  refine ⟨hmemA, ?_⟩
  have hprod : (⟨_, hmemA⟩ : ↥A) = ⟨d⁻¹, hdinvA⟩ * ⟨_, hmem⟩ := Subtype.ext hquot
  rw [hprod]
  refine IsUnit.mul ?_ hu
  exact ⟨⟨⟨d⁻¹, hdinvA⟩, ⟨d, hdA⟩, Subtype.ext (inv_mul_cancel₀ hd0), Subtype.ext (mul_inv_cancel₀ hd0)⟩, rfl⟩

end Ws23.SlopeLaw0

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type*} [Field Fbar0] [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar p) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An : Annulus A ↥(modularFunctionFieldBar p))
    (hparam : An.param = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (y : AlgebraicClosure ℚ)))))
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar p))
        (h₂ : ((frickeInvolutionBar p g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar p)) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar p g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar p)) (hf : f ∈ C0.integers), C0.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x0.ord (C0.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) :=
  Ws23.SlopeLaw0.slopeLaw_ssAnnulus_zeroChart_aux p A hp5 p (Nat.one_mul p).symm C0 x0 a ha ha2 h0 h1728 An hparam hdom
    hunit0 hordres0

end
end S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ
end P2MW
export P2MW.S_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_univ (solution)
