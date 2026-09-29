-- Prove2me | solution 1 for ModularCurve.slopeLaw_oppAnnulus_inftyChart_of_chartSpec
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a20ceeb3-d742-51c7-ad15-57dd1cc15798

import Mathlib
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
import Theorems.Thm_ModularCurve_NodeLocalized_gaussData_nodeCoord
import Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec
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

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec.ModularCurve"

namespace Ws23
namespace TwoBranchCore

p2m_open "IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec.ModularCurve ModularCurve.CharPReduction"

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

theorem evalAt_smul (v : Place K F) (hv : v.IsRational) (c : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' c) hf, v.evalAt_algebraMap_eq]

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
p2m_export "AlgebraicCurve" "Place Place.deg Place.ord Place.ord_mul Place.ord_inv Place.ord_zpow ComponentChart Annulus ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul"
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

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC qExpand jq jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar modularFunctionFieldBar ssJSet charLGeomPlaceOfPoint NodeLocalized.gaussData_nodeCoord NodeLocalized.isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit NodeLocalized.exists_hasValue_nodeCoord_of_centred deg_eq_one_modularFunctionFieldBar"
p2m_open "ModularCurve"
namespace SSAnnuliProof
p2m_open "IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec.AlgebraicCurve"

set_option maxHeartbeats 1600000 in

theorem slopeLaw_opp_aux (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (hp5 : 5 ≤ p) (n : ℕ) [NeZero n] (hn : n = 1 * p)
    {Fbari : Type} [Field Fbari] [Algebra (ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar n) Fbari)
    (xi : Place (ResidueField ↥A) Fbari)
    (a : ResidueField ↥A) (ha : a ∈ ssJSet p (ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An' : Annulus A ↥(modularFunctionFieldBar n))
    (hparam' : An'.param * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full n (dvd_refl n))⟩ :
                modularFunctionFieldBar n)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full n (jq_mem n))⟩ : modularFunctionFieldBar n) ^ p)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar n) (p : AlgebraicClosure ℚ))
    (hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar n), W ∈ An'.dom ↔
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
    (hunit : ∀ (g : ↥(modularFunctionFieldBar n))
        (h₁ : ((g : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 → ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar n)) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar n)) (hf : f ∈ Ci.integers), Ci.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An'.dom, P.ord f = 0) →
      ∀ P ∈ An'.dom,
        ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(xi.ord (Ci.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by

  subst hn
  intro f hf hfres hford P hP
  have hker : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hfres
    have : (⟨0, hf⟩ : Ci.integers) = 0 := rfl
    rw [this, map_zero]
  have hfordC : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0 :=
    fun W hW => hford W ((hdom' W).mpr hW)

  obtain ⟨c, hc0, m, h₁, h₂, h₁F, h₁u, h₂u, hord⟩ :=
    ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
      (IsLocalRing.residue ↥A) hker hp5 a ha ha2 h0 h1728 f hf0 hfordC

  obtain ⟨hgC, hgres⟩ := hunit (c • f) h₁ h₁u
  obtain ⟨hcA, hcinvA⟩ := Ci.const_mem_of_smul_unit hf hfres hgC hgres
  have hcunit : IsUnit (⟨c, hcA⟩ : ↥A) :=
    ⟨⟨⟨c, hcA⟩, ⟨c⁻¹, hcinvA⟩, Subtype.ext (mul_inv_cancel₀ hc0), Subtype.ext (inv_mul_cancel₀ hc0)⟩, rfl⟩

  have hordf : xi.ord (Ci.residue ⟨f, hf⟩) = -m := by
    rw [← Ci.ord_residue_smul_eq xi hf hcA hcunit hgC, hordresi (c • f) hgC h₁ h₁F]
    exact hord
  rw [hordf, neg_neg]

  have hPc : ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))) := (hdom' P).mp hP
  have hcore :=
    Ws23.TwoBranchCore.isUnit_evalAt_smul_mul_zpow_of_twoBranch (IsLocalRing.residue ↥A) hker hp5 a ha ha2
      h0 h1728 f c hc0 m h₁ h₁u h₂ h₂u hfordC P hPc

  have hG0 : ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p) ≠ 0 := by
    intro hG
    apply hp0
    have h := hparam'
    rw [hG, mul_zero] at h
    exact ((map_eq_zero _).mp h.symm)
  have hzeq : An'.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ)
      * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p)⁻¹ := by
    rw [← hparam', mul_assoc, mul_inv_cancel₀ hG0, mul_one]
  rw [hzeq]
  obtain ⟨hHA, hHunit⟩ := hcore

  obtain ⟨hPrat, -, -, -, -⟩ := An'.mem_dom P hP
  have hfP : f ∈ P.toValuationSubring := P.mem_toValuationSubring_of_ord_nonneg_alt hf0 (hford P hP).ge
  have hquot : P.evalAt f * P.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ)
        * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p)⁻¹) ^ m
      = c⁻¹ * (P.evalAt (c • f) * P.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ)
        * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p)⁻¹) ^ m) := by
    rw [Ws23.TwoBranchCore.evalAt_smul P hPrat c hfP, mul_assoc, ← mul_assoc c⁻¹, inv_mul_cancel₀ hc0]
    exact (one_mul _).symm
  have hmemA : P.evalAt f * P.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ)
        * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p)⁻¹) ^ m ∈ A := by
    rw [hquot]; exact mul_mem hcinvA hHA
  refine ⟨hmemA, ?_⟩
  have hprod : (⟨_, hmemA⟩ : ↥A) = ⟨c⁻¹, hcinvA⟩ * ⟨_, hHA⟩ := Subtype.ext hquot
  rw [hprod]
  refine IsUnit.mul ?_ hHunit
  exact ⟨⟨⟨c⁻¹, hcinvA⟩, ⟨c, hcA⟩, Subtype.ext (inv_mul_cancel₀ hc0), Subtype.ext (mul_inv_cancel₀ hc0)⟩, rfl⟩

end SSAnnuliProof
end ModularCurve

open IsLocalRing in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbari : Type} [Field Fbari] [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar p) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (An' : Annulus A ↥(modularFunctionFieldBar p))
    (hparam' : An'.param * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩ :
                modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (p : AlgebraicClosure ℚ))
    (hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), W ∈ An'.dom ↔
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
    (hunit : ∀ (g : ↥(modularFunctionFieldBar p))
        (h₁ : ((g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 → ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar p)) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar p) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized p A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom p A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar p)) (hf : f ∈ Ci.integers), Ci.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An'.dom, P.ord f = 0) →
      ∀ P ∈ An'.dom,
        ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(xi.ord (Ci.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) :=
  ModularCurve.SSAnnuliProof.slopeLaw_opp_aux p A hp5 p (Nat.one_mul p).symm Ci xi a ha ha2 h0 h1728 An' hparam'
    hdom' hunit hordresi

end S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec
end P2MW
export P2MW.S_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec (solution)
