-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_pFibre_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2ebc82a4-6482-5030-ae6f-4d008074f21a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Theorems.Thm_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_sum_inv_jWidth_of_ssJSetHasse
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_ModularCurve_ssJSetHasse_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

open ModularCurve AlgebraicCurve Polynomial

namespace HPGLUE

theorem mem_valuationSubring_of_isIntegral_adjoin {F : Type*} [Field F] (W : ValuationSubring F) (j x : F)
    (hj : j ∈ W) (hx : IsIntegral (Algebra.adjoin ℤ ({j} : Set F)) x) : x ∈ W := by
  have hsub : ∀ y ∈ Algebra.adjoin ℤ ({j} : Set F), y ∈ W := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.mp hz]; exact hj
    | algebraMap r => exact intCast_mem W.toSubring r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  let φ : Algebra.adjoin ℤ ({j} : Set F) →+* W :=
    { toFun := fun y => ⟨y.1, hsub y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hxW : IsIntegral W x := by
    have := hx.map_of_comp_eq φ (RingHom.id F) (RingHom.ext fun y => rfl)
    simpa using this
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := F)).mp hxW
  rw [← hy]
  exact y.2

theorem not_mem_nonunits_of_inv_mem {F : Type*} [Field F] (W : ValuationSubring F) {x : F}
    (hx0 : x ≠ 0) (hxi : x⁻¹ ∈ W) : x ∉ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt]
  have h1 : W.valuation x⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr hxi
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero W.valuation).mpr hx0))).mp h1

theorem mem_nonunits_of_inv_not_mem {F : Type*} [Field F] (W : ValuationSubring F) {x : F}
    (hx : x ∈ W) (hxi : x⁻¹ ∉ W) : x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  rw [← W.valuation_le_one_iff, not_le, map_inv₀] at hxi
  have hx0 : W.valuation x ≠ 0 := by
    intro h; rw [h, inv_zero] at hxi; exact not_lt_of_ge zero_le_one hxi
  exact (one_lt_inv₀ (zero_lt_iff.mpr hx0)).mp hxi

theorem inv_not_mem_of_mem_nonunits {F : Type*} [Field F] (W : ValuationSubring F) {x : F}
    (hx : x ∈ W.nonunits) (hx0 : x ≠ 0) : x⁻¹ ∉ W := fun h =>
  not_mem_nonunits_of_inv_mem W hx0 h hx

theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (f : A →+* B) (x : A) (q : Polynomial ℤ) :
    f (Polynomial.aeval x q) = Polynomial.aeval (f x) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

set_option synthInstance.maxHeartbeats 800000 in

theorem isIntegral_adjoin_trans {F : Type*} [Field F] {a b x : F}
    (hb : IsIntegral (Algebra.adjoin ℤ ({a} : Set F)) b) (hx : IsIntegral (Algebra.adjoin ℤ ({b} : Set F)) x) :
    IsIntegral (Algebra.adjoin ℤ ({a} : Set F)) x := by
  have hbC : b ∈ integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F := hb
  have hle : Algebra.adjoin ℤ ({b} : Set F) ≤ (integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F).restrictScalars ℤ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hbC)
  let φ : Algebra.adjoin ℤ ({b} : Set F) →+* integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F :=
    { toFun := fun y => ⟨y.1, hle y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hxC : IsIntegral (integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F) x := by
    have := hx.map_of_comp_eq φ (RingHom.id F) (RingHom.ext fun y => rfl)
    simpa using this
  exact isIntegral_trans (R := Algebra.adjoin ℤ ({a} : Set F))
    (A := integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F) x hxC

theorem isIntegral_adjoin_map {F : Type*} [Field F] [Algebra ℚ F] (σ : F ≃ₐ[ℚ] F) {x y : F}
    (h : IsIntegral (Algebra.adjoin ℤ ({x} : Set F)) y) :
    IsIntegral (Algebra.adjoin ℤ ({σ x} : Set F)) (σ y) := by
  have hsub : ∀ z ∈ Algebra.adjoin ℤ ({x} : Set F), σ z ∈ Algebra.adjoin ℤ ({σ x} : Set F) := by
    intro z hz
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz ⊢
    have hz' : ∃ S, Polynomial.aeval x S = z := hz
    obtain ⟨S, rfl⟩ := hz'
    exact ⟨S, (map_aeval_int σ.toRingEquiv.toRingHom x S).symm⟩
  let φ : Algebra.adjoin ℤ ({x} : Set F) →+* Algebra.adjoin ℤ ({σ x} : Set F) :=
    { toFun := fun z => ⟨σ z, hsub z z.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun a b => Subtype.ext (map_mul σ _ _)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun a b => Subtype.ext (map_add σ _ _) }
  exact h.map_of_comp_eq φ σ.toRingEquiv.toRingHom (RingHom.ext fun z => rfl)

theorem exists_finset_ssJSet_sum_eq (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (κ : Type*) [Field κ] [IsAlgClosed κ]
    [CharP κ p] [DecidableEq κ] :
    ∃ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) ∧ ∑ a ∈ S, 12 / jWidth a = p - 1 := by
  have hp2 : p ≠ 2 := by omega
  have hfin : (ssJSet p κ).Finite := by rw [ssJSet_eq_ssJSetHasse p hp2 κ]; exact ssJSetHasse_finite p hp2 κ
  refine ⟨hfin.toFinset, fun a => hfin.mem_toFinset, ?_⟩
  have hS' : ∀ j, j ∈ hfin.toFinset ↔ j ∈ ssJSetHasse p κ := fun j => by
    rw [hfin.mem_toFinset, ssJSet_eq_ssJSetHasse p hp2 κ]
  have hsum := sum_inv_jWidth_of_ssJSetHasse p hp κ hfin.toFinset hS'

  have hdiv : ∀ a : κ, ((12 / jWidth a : ℕ) : ℚ) = 12 * ((jWidth a : ℚ))⁻¹ := by
    intro a
    rcases jWidth_eq_one_or a with h | h | h <;> rw [h] <;> norm_num
  have hcast : ((∑ a ∈ hfin.toFinset, 12 / jWidth a : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sum]
    simp_rw [hdiv, ← Finset.mul_sum, hsum]
    ring
  have hp1 : 1 ≤ p := by omega
  have : ((∑ a ∈ hfin.toFinset, 12 / jWidth a : ℕ) : ℚ) = ((p - 1 : ℕ) : ℚ) := by
    rw [hcast, Nat.cast_sub hp1, Nat.cast_one]
  exact_mod_cast this

theorem derivative_ne_zero_of_natDegree (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (U : Polynomial (ZMod p))
    (hU : U.natDegree = p - 1) : Polynomial.derivative U ≠ 0 := by
  intro h
  have hc := congrArg (fun P => P.coeff (p - 2)) h
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  have h12 : p - 2 + 1 = p - 1 := by omega
  rw [h12] at hc
  have hlc : U.coeff (p - 1) ≠ 0 := by
    rw [← hU]; exact Polynomial.leadingCoeff_ne_zero.mpr (fun h0 => by rw [h0, Polynomial.natDegree_zero] at hU; omega)
  have hcast : ((p - 2 : ℕ) : ZMod p) + 1 ≠ 0 := by
    have : ((p - 2 : ℕ) : ZMod p) + 1 = ((p - 1 : ℕ) : ZMod p) := by
      rw [← h12, Nat.cast_succ]
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  exact mul_ne_zero hlc hcast hc

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem hp_main (hp : 5 ≤ p) (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : HpoolLevelRing.Afin p)
    (hv : (v : ↥(modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∨
      (v : ↥(modularFunctionFieldFull p)) = (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹) :
    ∃ (Pu Pz : Ideal (HpoolLevelRing.Afin p)),
      Pu.IsPrime ∧ Pz.IsPrime ∧ Pu ≠ Pz ∧
      (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {Pu, Pz} ∧
      Pu ⊓ Pz = Ideal.span {(p : HpoolLevelRing.Afin p)} ∧
      v ∉ Pu ∧ v ∈ Pz ∧
      ∃ (e : (HpoolLevelRing.Afin p ⧸ Pu) ≃+* Polynomial (ZMod p)) (U : Polynomial (ZMod p)),
        e (Ideal.Quotient.mk Pu v) = U ∧ U.natDegree = p - 1 ∧ Polynomial.derivative U ≠ 0 := by
  classical
  have hpp : p.Prime := Fact.out

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hne, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  have hM := DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
  obtain ⟨hgauss, σ, hσj, hσjp, hσσ, hσW⟩ :=
    DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
  obtain ⟨huA, hvA⟩ := modularUnitSeries_mem_chartAlgFin_int p hmem
  set uF : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, hmem⟩ with huF
  have hu0 : uF ≠ 0 := fun h => modularUnitSeries_ne_zero p (congrArg Subtype.val h)
  have hp0 : (p : ↥(modularFunctionFieldFull p)) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero

  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  have hjW₀ : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ W₀ := by simpa using (hgen 0 Polynomial.X hX).1
  have hjW₁ : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ W₁ := by simpa using (hgen 1 Polynomial.X hX).1
  have hAW₀ : ∀ a : HpoolLevelRing.Afin p, (a : ↥(modularFunctionFieldFull p)) ∈ W₀ :=
    fun a => mem_valuationSubring_of_isIntegral_adjoin W₀ _ _ hjW₀ a.2
  have hAW₁ : ∀ a : HpoolLevelRing.Afin p, (a : ↥(modularFunctionFieldFull p)) ∈ W₁ :=
    fun a => mem_valuationSubring_of_isIntegral_adjoin W₁ _ _ hjW₁ a.2

  let φ₀ : HpoolLevelRing.Afin p →+* W₀ :=
    { toFun := fun a => ⟨a, hAW₀ a⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φ₁ : HpoolLevelRing.Afin p →+* W₁ :=
    { toFun := fun a => ⟨a, hAW₁ a⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let P₀ : Ideal (HpoolLevelRing.Afin p) := (IsLocalRing.maximalIdeal W₀).comap φ₀
  let P₁ : Ideal (HpoolLevelRing.Afin p) := (IsLocalRing.maximalIdeal W₁).comap φ₁
  have hP₀ : ∀ a : HpoolLevelRing.Afin p, a ∈ P₀ ↔ (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits := fun a => by
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
  have hP₁ : ∀ a : HpoolLevelRing.Afin p, a ∈ P₁ ↔ (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits := fun a => by
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
  haveI : P₀.IsPrime := Ideal.comap_isPrime φ₀ _
  haveI : P₁.IsPrime := Ideal.comap_isPrime φ₁ _

  have hp1 : ¬ p ∣ 1 := fun h => hpp.one_lt.ne' (Nat.dvd_one.mp h)
  obtain ⟨W', h1, h2, -⟩ := exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd 1 p hp1
  have hmem₁ : modularUnitSeries p ∈ modularFunctionFieldFull (1 * p) :=
    full_degeneracy_le (N := p) (M := 1 * p) ⟨1, by ring⟩ hmem
  obtain ⟨⟨x, hx0, hxu⟩, -, -, -⟩ :=
    modularUnitSeries_mem_valuationSubring_pair_of_not_dvd 1 p hp1 hmem₁ (W' 0) (W' 1) h1 h2

  have huW₀ : uF ∈ W₀ := (hgauss uF).mpr ⟨x, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one, ← hxu]⟩
  have huiW₀ : uF⁻¹ ∈ W₀ := (hgauss uF⁻¹).mpr ⟨1, x, hx0, by
    rw [map_one, ← hxu]; exact inv_mul_cancel₀ (modularUnitSeries_ne_zero p)⟩
  have hpW₀ : (p : ↥(modularFunctionFieldFull p)) ∈ W₀ := natCast_mem W₀ p
  have hpiW₀ : (p : ↥(modularFunctionFieldFull p))⁻¹ ∉ W₀ := inv_not_mem_of_mem_nonunits W₀ hp₀ hp0

  have hwex := exists_isFrickeAutFull_of_neZero p
  set w := frickeInvolutionFull p with hwdef
  have hw : IsFrickeAutFull p w := isFrickeAutFull_frickeInvolutionFull p hwex
  have hjF1 : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) = ⟨qExpand ℚ 1 jq, jqd_mem_full p (Dvd.intro p (one_mul p))⟩ :=
    Subtype.ext (show (IgusaScheme.jFull p : LaurentSeries ℚ) = qExpand ℚ 1 jq by rw [qExpand_one_apply]; rfl)
  have hjpF : (jp : ↥(modularFunctionFieldFull p)) = ⟨qExpand ℚ p jq, jqd_mem_full p (Dvd.intro_left 1 (one_mul p))⟩ := Subtype.ext hjp
  have hσw : ∀ z : ↥(modularFunctionFieldFull p), σ z = w z := by

    have hgen_eq : ∀ (x : LaurentSeries ℚ) (hx : x ∈ divisorExpansions p),
        σ ⟨x, IntermediateField.subset_adjoin ℚ _ hx⟩ = w ⟨x, IntermediateField.subset_adjoin ℚ _ hx⟩ := by
      intro x hx
      obtain ⟨d, hd, hdp, rfl⟩ := hx
      rcases (Nat.dvd_prime hpp).mp hdp with h1 | h1
      ·
        have e1 : (⟨qExpand ℚ d jq, IntermediateField.subset_adjoin ℚ _ ⟨d, hd, hdp, rfl⟩⟩ : ↥(modularFunctionFieldFull p)) =
            IgusaScheme.jFull p :=
          Subtype.ext (show qExpand ℚ d jq = (IgusaScheme.jFull p : LaurentSeries ℚ) by
            rw [qExpand_congr h1, qExpand_one_apply]; rfl)
        have e2 := hw 1 p (one_mul p) inferInstance inferInstance
        rw [← hjF1, ← hjpF] at e2
        rw [e1, hσj, e2]
      ·
        have e1 : (⟨qExpand ℚ d jq, IntermediateField.subset_adjoin ℚ _ ⟨d, hd, hdp, rfl⟩⟩ : ↥(modularFunctionFieldFull p)) = (jp : ↥(modularFunctionFieldFull p)) :=
          Subtype.ext (show qExpand ℚ d jq = ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) by rw [qExpand_congr h1]; exact hjp.symm)
        have e2 := hw p 1 (mul_one p) inferInstance inferInstance
        rw [← hjF1, ← hjpF] at e2
        rw [e1, hσjp, e2]
    intro z
    obtain ⟨x, hx⟩ := z
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hgen_eq x hx
    | algebraMap r =>
      have : (⟨algebraMap ℚ (LaurentSeries ℚ) r, IntermediateField.algebraMap_mem _ r⟩ : ↥(modularFunctionFieldFull p)) = algebraMap ℚ ↥(modularFunctionFieldFull p) r :=
        Subtype.ext (by simp)
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, add_mem hx hy⟩ : ↥(modularFunctionFieldFull p)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
    | inv x hx ihx =>
      have : (⟨x⁻¹, inv_mem hx⟩ : ↥(modularFunctionFieldFull p)) = (⟨x, hx⟩ : ↥(modularFunctionFieldFull p))⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihx]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, mul_mem hx hy⟩ : ↥(modularFunctionFieldFull p)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

  set vF : ↥(modularFunctionFieldFull p) := (p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹ with hvF
  have hinj : Function.Injective (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) := (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).injective
  have hcoe : ∀ z : ↥(modularFunctionFieldFull p), algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ) z = (z : LaurentSeries ℚ) := fun z => rfl
  have hσu : σ uF = vF := by
    rw [hσw]
    apply hinj
    have h1 := coe_frickeInvolutionFull_modularUnitSeries_of_neZero p hmem
    rw [← hwdef] at h1
    rw [hcoe, h1, hvF, map_mul, map_pow, map_inv₀, map_natCast, hcoe uF]
    have hC : (HahnSeries.C ((p : ℚ) ^ 12) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 := by
      rw [map_pow, map_natCast]
    first
      | rw [Algebra.smul_def, ← HahnSeries.C_eq_algebraMap, hC]
      | rw [← HahnSeries.C_mul_eq_smul, hC]
  have hv0 : vF ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) (inv_ne_zero hu0)

  have hvW₀ : vF ∈ W₀ := mul_mem (pow_mem hpW₀ 12) huiW₀
  have hviW₀ : vF⁻¹ ∉ W₀ := by
    intro h
    apply hpiW₀
    have key : (p : ↥(modularFunctionFieldFull p))⁻¹ = vF⁻¹ * uF⁻¹ * (p : ↥(modularFunctionFieldFull p)) ^ 11 := by
      rw [hvF]; field_simp
    rw [key]
    exact mul_mem (mul_mem h huiW₀) (pow_mem hpW₀ 11)
  have huW₁ : uF ∈ W₁ := (hσW uF).mpr (by rw [hσu]; exact hvW₀)
  have huiW₁ : uF⁻¹ ∉ W₁ := fun h => hviW₀ (by
    have := (hσW uF⁻¹).mp h
    rwa [map_inv₀, hσu] at this)
  have hσv : σ vF = uF := by
    rw [hvF, map_mul, map_pow, map_natCast, map_inv₀, hσu, hvF]
    field_simp
  have hvW₁ : vF ∈ W₁ := (hσW vF).mpr (by rw [hσv]; exact huW₀)
  have hviW₁ : vF⁻¹ ∈ W₁ := (hσW vF⁻¹).mpr (by rw [map_inv₀, hσv]; exact huiW₀)

  let uA : HpoolLevelRing.Afin p := ⟨uF, huA⟩
  let vA : HpoolLevelRing.Afin p := ⟨vF, hvA⟩
  have huP₀ : uA ∉ P₀ := fun h => not_mem_nonunits_of_inv_mem W₀ hu0 huiW₀ ((hP₀ uA).mp h)
  have huP₁ : uA ∈ P₁ := (hP₁ uA).mpr (mem_nonunits_of_inv_not_mem W₁ huW₁ huiW₁)
  have hvP₀ : vA ∈ P₀ := (hP₀ vA).mpr (mem_nonunits_of_inv_not_mem W₀ hvW₀ hviW₀)
  have hvP₁ : vA ∉ P₁ := fun h => not_mem_nonunits_of_inv_mem W₁ hv0 hviW₁ ((hP₁ vA).mp h)
  have hneP : P₀ ≠ P₁ := fun h => huP₀ (h ▸ huP₁)

  have hmin : (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {P₀, P₁} := by
    ext 𝔭
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hM𝔭 := hM 𝔭
    rw [hM𝔭]
    constructor
    · rintro (h | h)
      · left; exact Ideal.ext fun a => (h a).trans (hP₀ a).symm
      · right; exact Ideal.ext fun a => (h a).trans (hP₁ a).symm
    · rintro (rfl | rfl)
      · left; exact fun a => hP₀ a
      · right; exact fun a => hP₁ a

  have hrad : P₀ ⊓ P₁ = Ideal.span {(p : HpoolLevelRing.Afin p)} := by
    have hred := (DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int p).1
    have hr : (Ideal.span {(p : HpoolLevelRing.Afin p)}).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).mpr hred
    rw [← hr.radical, ← Ideal.sInf_minimalPrimes, hmin, sInf_pair]

  obtain ⟨hS1, -⟩ := DRModel.exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair p jp hjp W₀ W₁
    hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁
  obtain ⟨e₀, he₀j, -⟩ := hS1 P₀ hP₀

  set U : Polynomial (ZMod p) := e₀ (Ideal.Quotient.mk P₀ uA) with hUdef
  have hdegU : U.natDegree = p - 1 := by
    let κ := AlgebraicClosure (ZMod p)
    haveI : CharP κ p := charP_of_injective_algebraMap (algebraMap (ZMod p) κ).injective p
    obtain ⟨S, hS, hsum⟩ := exists_finset_ssJSet_sum_eq p hp κ
    have hmap := DRModel.map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet p hp W₀ hgauss P₀ hP₀ e₀ he₀j uA rfl κ S hS
    have h1 : U.natDegree = (U.map (ZMod.castHom (dvd_refl p) κ)).natDegree :=
      (Polynomial.natDegree_map_eq_of_injective (ZMod.castHom (dvd_refl p) κ).injective U).symm
    rw [h1, hUdef, hmap, Polynomial.natDegree_prod_of_monic _ _ (fun a _ => (Polynomial.monic_X_sub_C a).pow _)]
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    exact hsum
  have hderU : Polynomial.derivative U ≠ 0 := derivative_ne_zero_of_natDegree p hp U hdegU

  rcases hv with hvu | hvv
  ·
    have hv_eq : v = uA := Subtype.ext hvu
    subst hv_eq
    exact ⟨P₀, P₁, inferInstance, inferInstance, hneP, hmin, hrad, huP₀, huP₁, e₀, U, rfl, hdegU, hderU⟩
  ·
    have hv_eq : v = vA := Subtype.ext hvv
    subst hv_eq

    have hσA : ∀ a : HpoolLevelRing.Afin p, IsIntegral (Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) (σ (a : ↥(modularFunctionFieldFull p))) := by
      intro a
      have h1 : IsIntegral (Algebra.adjoin ℤ ({σ (IgusaScheme.jFull p)} : Set ↥(modularFunctionFieldFull p))) (σ (a : ↥(modularFunctionFieldFull p))) :=
        isIntegral_adjoin_map σ a.2
      rw [hσj] at h1
      exact isIntegral_adjoin_trans jp.2 h1
    let σA : HpoolLevelRing.Afin p →+* HpoolLevelRing.Afin p :=
      { toFun := fun a => ⟨σ (a : ↥(modularFunctionFieldFull p)), hσA a⟩
        map_one' := Subtype.ext (map_one σ)
        map_mul' := fun a b => Subtype.ext (map_mul σ _ _)
        map_zero' := Subtype.ext (map_zero σ)
        map_add' := fun a b => Subtype.ext (map_add σ _ _) }
    have hσA2 : ∀ a, σA (σA a) = a := fun a => Subtype.ext (hσσ _)

    have hnu : ∀ f : ↥(modularFunctionFieldFull p), f ∈ W₁.nonunits ↔ σ f ∈ W₀.nonunits := by
      intro f
      rcases eq_or_ne f 0 with rfl | hf0
      · rw [map_zero]
        simp [ValuationSubring.mem_nonunits_iff]
      · have hσf0 : σ f ≠ 0 := fun h => hf0 (σ.injective (h.trans (map_zero σ).symm))
        constructor
        · intro h
          have hfW : f ∈ W₁ := ValuationSubring.nonunits_le h
          exact mem_nonunits_of_inv_not_mem W₀ ((hσW f).mp hfW)
            (fun hi => inv_not_mem_of_mem_nonunits W₁ h hf0 ((hσW f⁻¹).mpr (by rwa [map_inv₀])))
        · intro h
          have hfW : σ f ∈ W₀ := ValuationSubring.nonunits_le h
          exact mem_nonunits_of_inv_not_mem W₁ ((hσW f).mpr hfW)
            (fun hi => inv_not_mem_of_mem_nonunits W₀ h hσf0 (by rw [← map_inv₀]; exact (hσW f⁻¹).mp hi))
    have hle₁ : P₁ ≤ P₀.comap σA := by
      intro a ha
      rw [Ideal.mem_comap, hP₀]
      show σ (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits
      exact (hnu _).mp ((hP₁ a).mp ha)
    have hle₀ : P₀ ≤ P₁.comap σA := by
      intro a ha
      rw [Ideal.mem_comap, hP₁]
      show σ (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits
      rw [hnu, hσσ]
      exact (hP₀ a).mp ha
    let φf : (HpoolLevelRing.Afin p ⧸ P₁) →+* (HpoolLevelRing.Afin p ⧸ P₀) := Ideal.quotientMap P₀ σA hle₁
    let φb : (HpoolLevelRing.Afin p ⧸ P₀) →+* (HpoolLevelRing.Afin p ⧸ P₁) := Ideal.quotientMap P₁ σA hle₀
    have hfb : φb.comp φf = RingHom.id _ := by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, RingHom.id_apply, φf, φb, Ideal.quotientMap_mk, hσA2]
    have hbf : φf.comp φb = RingHom.id _ := by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, RingHom.id_apply, φf, φb, Ideal.quotientMap_mk, hσA2]
    let e₁ : (HpoolLevelRing.Afin p ⧸ P₁) ≃+* Polynomial (ZMod p) := (RingEquiv.ofRingHom φf φb hbf hfb).trans e₀
    have he₁ : e₁ (Ideal.Quotient.mk P₁ vA) = U := by
      show e₀ (φf (Ideal.Quotient.mk P₁ vA)) = U
      have h1 : φf (Ideal.Quotient.mk P₁ vA) = Ideal.Quotient.mk P₀ (σA vA) := Ideal.quotientMap_mk
      have h2 : σA vA = uA := Subtype.ext hσv
      rw [h1, h2]
    refine ⟨P₁, P₀, inferInstance, inferInstance, hneP.symm, ?_, ?_, hvP₁, hvP₀, e₁, U, he₁, hdegU, hderU⟩
    · rw [hmin, Set.pair_comm]
    · rw [inf_comm, hrad]

end HPGLUE

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p) (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : HpoolLevelRing.Afin p)
    (hv : (v : ↥(ModularCurve.modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∨
      (v : ↥(ModularCurve.modularFunctionFieldFull p)) = (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p))⁻¹) :
    ∃ (Pu Pz : Ideal (HpoolLevelRing.Afin p)),
      Pu.IsPrime ∧ Pz.IsPrime ∧ Pu ≠ Pz ∧
      (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {Pu, Pz} ∧
      Pu ⊓ Pz = Ideal.span {(p : HpoolLevelRing.Afin p)} ∧
      v ∉ Pu ∧ v ∈ Pz ∧
      ∃ (e : (HpoolLevelRing.Afin p ⧸ Pu) ≃+* Polynomial (ZMod p)) (U : Polynomial (ZMod p)),
        e (Ideal.Quotient.mk Pu v) = U ∧ U.natDegree = p - 1 ∧ Polynomial.derivative U ≠ 0 :=
  HPGLUE.hp_main p hp hmem v hv

end S_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary (solution)
