-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1b2ae020-1e7b-5dff-b06c-757375d9a46f

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_Polynomial_finite_setOf_criticalValue
import Theorems.Thm_Polynomial_separable_sub_C_of_forall_eval_derivative
import Theorems.Thm_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
import Theorems.Thm_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
import Theorems.Thm_ModularCurve_HpoolLevelRing_finite_levelRing
import Theorems.Thm_ModularCurve_HpoolLevelRing_rankAtStalk_levelRing_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial IsLocalRing

universe u

noncomputable section

namespace LevelBC

variable (A : Type) [CommRing A] (c d : ℤ) (u : A) (g : ℤ[X])

abbrev Aaway (r : ℤ) : Type := Localization.Away (algebraMap ℤ A r)

abbrev Br (r : ℤ) : Type := Aaway A r ⧸ Ideal.span {aeval (algebraMap A (Aaway A r) u) g}

scoped instance algAway (r : ℤ) : Algebra (Localization.Away r) (Aaway A r) := (Localization.awayMap (algebraMap ℤ A) r).toAlgebra

scoped instance algAwayBr (r : ℤ) : Algebra (Localization.Away r) (Br A u g r) := Ideal.Quotient.algebra _

theorem ringHom_away_ext {r : ℤ} {X : Type*} [CommRing X] (f₁ f₂ : Localization.Away r →+* X) : f₁ = f₂ :=
  IsLocalization.ringHom_ext (Submonoid.powers r) (Subsingleton.elim _ _)

section maps

noncomputable def φA : Aaway A c →+* Aaway A (c * d) :=
  IsLocalization.Away.lift (algebraMap ℤ A c) (S := Aaway A c)
    (isUnit_of_dvd_unit (map_dvd (algebraMap A (Aaway A (c * d))) (map_dvd (algebraMap ℤ A) (dvd_mul_right c d)))
      (IsLocalization.Away.algebraMap_isUnit (algebraMap ℤ A (c * d))))

theorem φA_algebraMap (a : A) : φA A c d (algebraMap A _ a) = algebraMap A _ a :=
  IsLocalization.Away.lift_eq _ _ a

end maps

section instances

noncomputable scoped instance algAA : Algebra (Aaway A c) (Aaway A (c * d)) := (φA A c d).toAlgebra

noncomputable scoped instance algRR : Algebra (Localization.Away c) (Localization.Away (c * d)) := algAA ℤ c d

scoped instance istAAA : IsScalarTower A (Aaway A c) (Aaway A (c * d)) :=
  IsScalarTower.of_algebraMap_eq (fun a => (φA_algebraMap A c d a).symm)

noncomputable scoped instance algRA' : Algebra (Localization.Away c) (Aaway A (c * d)) :=
  ((algebraMap (Localization.Away (c * d)) (Aaway A (c * d))).comp
    (algebraMap (Localization.Away c) (Localization.Away (c * d)))).toAlgebra

scoped instance istRAA : IsScalarTower (Localization.Away c) (Aaway A c) (Aaway A (c * d)) :=
  IsScalarTower.of_algebraMap_eq' (ringHom_away_ext _ _)

scoped instance istRRA : IsScalarTower (Localization.Away c) (Localization.Away (c * d)) (Aaway A (c * d)) :=
  IsScalarTower.of_algebraMap_eq' (ringHom_away_ext _ _)

scoped instance isLocA : IsLocalization.Away (algebraMap ℤ (Aaway A c) d) (Aaway A (c * d)) := by
  classical

  have hzc : algebraMap ℤ (Aaway A c) d = algebraMap A (Aaway A c) (algebraMap ℤ A d) :=
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (Aaway A c)) ((algebraMap A (Aaway A c)).comp (algebraMap ℤ A))) d
  rw [IsLocalization.Away, hzc]
  set x : A := algebraMap ℤ A c with hx
  set y : A := algebraMap ℤ A d with hy
  set φ : A →+* Aaway A c := algebraMap A (Aaway A c) with hφ

  have h0 : IsLocalization (Submonoid.powers (x * y)) (Aaway A (c * d)) := by
    have : x * y = algebraMap ℤ A (c * d) := (map_mul (algebraMap ℤ A) c d).symm
    rw [this]; exact Localization.isLocalization

  set N : Submonoid A := Submonoid.powers x ⊔ Submonoid.powers y with hN
  have h1 : IsLocalization N (Aaway A (c * d)) := by
    refine @IsLocalization.of_le_of_exists_dvd A _ (Submonoid.powers (x * y)) (Aaway A (c * d)) _ _ h0 N ?_ ?_
    · rintro _ ⟨n, rfl⟩
      show (x * y) ^ n ∈ N
      rw [mul_pow]
      exact Submonoid.mul_mem_sup ⟨n, rfl⟩ ⟨n, rfl⟩
    · intro n hn
      obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.1 hn
      obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ha
      obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hb
      refine ⟨(x * y) ^ (i + j), ⟨i + j, rfl⟩, ?_⟩
      rw [mul_pow, pow_add, pow_add]
      exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_left _ _)

  have h2 : IsLocalization (N.map φ) (Aaway A (c * d)) :=
    haveI := h1
    IsLocalization.isLocalization_of_submonoid_le (S := Aaway A c) (T := Aaway A (c * d)) (Submonoid.powers x) N le_sup_left

  have hNmap : N.map φ = Submonoid.powers (φ x) ⊔ Submonoid.powers (φ y) := by
    rw [hN, Submonoid.map_sup, Submonoid.map_powers, Submonoid.map_powers]
  have hux : IsUnit (φ x) := IsLocalization.Away.algebraMap_isUnit x
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (φ y)) (N.map φ) ?_ ?_).mpr h2
  · rw [hNmap]; exact le_sup_right
  · intro n hn
    rw [hNmap] at hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.1 hn
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ha
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hb
    exact ⟨φ y ^ j, ⟨j, rfl⟩, ((hux.pow i).mul_left_dvd).2 dvd_rfl⟩

scoped instance isLocR : IsLocalization.Away (algebraMap ℤ (Localization.Away c) d) (Localization.Away (c * d)) :=
  isLocA ℤ c d

end instances

section quotient

theorem algebraMap_aeval_eq :
    algebraMap (Aaway A c) (Aaway A (c * d)) (aeval (algebraMap A (Aaway A c) u) g) =
      aeval (algebraMap A (Aaway A (c * d)) u) g := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_apply A]
  congr 1
  exact Subsingleton.elim _ _

theorem map_ideal_eq :
    (Ideal.span {aeval (algebraMap A (Aaway A c) u) g}).map (algebraMap (Aaway A c) (Aaway A (c * d))) =
      Ideal.span {aeval (algebraMap A (Aaway A (c * d)) u) g} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_aeval_eq]

theorem ideal_le_comap :
    Ideal.span {aeval (algebraMap A (Aaway A c) u) g} ≤
      (Ideal.span {aeval (algebraMap A (Aaway A (c * d)) u) g}).comap (algebraMap (Aaway A c) (Aaway A (c * d))) := by
  rw [← Ideal.map_le_iff_le_comap, map_ideal_eq]

noncomputable scoped instance algBB : Algebra (Br A u g c) (Br A u g (c * d)) :=
  (Ideal.quotientMap _ (algebraMap (Aaway A c) (Aaway A (c * d))) (ideal_le_comap A c d u g)).toAlgebra

scoped instance istRRB : @IsScalarTower (Localization.Away c) (Localization.Away (c * d)) (Br A u g (c * d))
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq' (Localization.Away c) (Localization.Away (c * d)) (Br A u g (c * d)) _ _ _ _ _ _
    (ringHom_away_ext _ _)

scoped instance istRBB' : @IsScalarTower (Localization.Away c) (Br A u g c) (Br A u g (c * d))
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq' (Localization.Away c) (Br A u g c) (Br A u g (c * d)) _ _ _ _ _ _
    (ringHom_away_ext _ _)

scoped instance isLocB : IsLocalization ((Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
    (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g}))) (Br A u g (c * d)) :=
  IsLocalization.of_surjective (Submonoid.powers (algebraMap ℤ (Aaway A c) d)) (Aaway A (c * d))
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    rfl (by rw [Ideal.mk_ker, Ideal.mk_ker, map_ideal_eq])

theorem submonoid_eq :
    Algebra.algebraMapSubmonoid (Br A u g c) (Submonoid.powers (algebraMap ℤ (Localization.Away c) d)) =
      (Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
        (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g})) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Submonoid.map_powers]
  congr 1
  exact RingHom.congr_fun (Subsingleton.elim ((algebraMap _ (Br A u g c)).comp (algebraMap ℤ (Localization.Away c)))
    ((Ideal.Quotient.mk _).comp (algebraMap ℤ (Aaway A c)))) d

scoped instance isPushoutB : Algebra.IsPushout (Localization.Away c) (Br A u g c) (Localization.Away (c * d)) (Br A u g (c * d)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (Br A u g c) (Submonoid.powers (algebraMap ℤ (Localization.Away c) d)))
      (Br A u g (c * d)) := by rw [submonoid_eq]; exact isLocB A c d u g
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers (algebraMap ℤ (Localization.Away c) d))
    (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d))

end quotient

section transfer

scoped instance isPIR (r : ℤ) : IsPrincipalIdealRing (Localization.Away r) where
  principal I := by
    obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal (I.under ℤ)).principal
    refine ⟨⟨algebraMap ℤ _ n, ?_⟩⟩
    rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) I, hn, Ideal.submodule_span_eq,
      Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

theorem isDomain_away {r : ℤ} (hr : r ≠ 0) : IsDomain (Localization.Away r) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)

variable {A c d u g}

theorem transfer (hcd : c * d ≠ 0) (n : ℕ)
    (hfin : Module.Finite (Localization.Away c) (Br A u g c))
    (het : Algebra.Etale (Localization.Away c) (Br A u g c))
    (hrk : ∀ 𝔮 : PrimeSpectrum (Localization.Away c), Module.rankAtStalk (R := Localization.Away c) (Br A u g c) 𝔮 = n) :
    Module.Finite (Localization.Away (c * d)) (Br A u g (c * d)) ∧
    Algebra.Etale (Localization.Away (c * d)) (Br A u g (c * d)) ∧
    Module.Free (Localization.Away (c * d)) (Br A u g (c * d)) ∧
    Module.finrank (Localization.Away (c * d)) (Br A u g (c * d)) = n ∧
    ∀ 𝔮 : PrimeSpectrum (Localization.Away (c * d)),
      Module.rankAtStalk (R := Localization.Away (c * d)) (Br A u g (c * d)) 𝔮 = n := by
  haveI := hfin; haveI := het
  haveI : Algebra.IsPushout (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d)) :=
    Algebra.IsPushout.symm inferInstance
  let e : TensorProduct (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) ≃ₐ[Localization.Away (c * d)]
      Br A u g (c * d) :=
    Algebra.IsPushout.equiv (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d))
  have hfin' : Module.Finite (Localization.Away (c * d)) (Br A u g (c * d)) := Module.Finite.equiv e.toLinearEquiv
  have het' : Algebra.Etale (Localization.Away (c * d)) (Br A u g (c * d)) := by
    have hloc : IsLocalization ((Submonoid.powers (algebraMap ℤ (Localization.Away c) d)).map
        (algebraMap (Localization.Away c) (Br A u g c))) (Br A u g (c * d)) := by
      rw [← Algebra.algebraMapSubmonoid, submonoid_eq]; exact isLocB A c d u g
    have hfe : Algebra.FormallyEtale (Localization.Away (c * d)) (Br A u g (c * d)) :=
      Algebra.FormallyEtale.localization_map (R := Localization.Away c) (S := Br A u g c)
        (Rₘ := Localization.Away (c * d)) (Sₘ := Br A u g (c * d))
        (Submonoid.powers (algebraMap ℤ (Localization.Away c) d))
    haveI := hfin'
    have hfp : Algebra.FinitePresentation (Localization.Away (c * d)) (Br A u g (c * d)) :=
      (Algebra.FinitePresentation.of_finiteType (R := Localization.Away (c * d)) (A := Br A u g (c * d))).mp inferInstance
    exact ⟨hfe, hfp⟩
  have hrk' : ∀ 𝔮 : PrimeSpectrum (Localization.Away (c * d)),
      Module.rankAtStalk (R := Localization.Away (c * d)) (Br A u g (c * d)) 𝔮 = n := fun 𝔮 => by
    rw [Algebra.rankAtStalk_eq_of_isPushout (Localization.Away c) (Br A u g c) (Localization.Away (c * d)) (Br A u g (c * d)) 𝔮]
    exact hrk _
  haveI := hfin'; haveI := het'
  haveI : IsDomain (Localization.Away (c * d)) := isDomain_away hcd
  haveI : Module.Free (Localization.Away (c * d)) (Br A u g (c * d)) := inferInstance
  refine ⟨hfin', het', inferInstance, ?_, hrk'⟩
  have h := Module.rankAtStalk_eq_finrank_of_free (R := Localization.Away (c * d)) (M := Br A u g (c * d))
  have := hrk' ⟨⊥, Ideal.isPrime_bot⟩
  rw [h] at this
  exact this

end transfer

section torsion

variable {A c d u g}

theorem smul_eq_zero_of_pow_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {π n : R}
    (hπ : ∀ m : M, π • m = 0 → m = 0) (a : ℕ) {t : M} (h : (π ^ a * n) • t = 0) : n • t = 0 := by
  induction a with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    apply hπ
    rw [← mul_smul, ← mul_assoc, ← pow_succ']
    exact h

theorem exists_int_kills_torsion (hc : c ≠ 0) (p : ℕ) (hp : p.Prime)
    (hfin : Module.Finite (Localization.Away c) (Br A u g c))
    (hpt : ∀ s : Br A u g c, (p : Br A u g c) * s = 0 → s = 0) :
    ∃ n' : ℤ, n' ≠ 0 ∧ ¬ (p : ℤ) ∣ n' ∧
      ∀ s : Br A u g c, s ∈ Submodule.torsion (Localization.Away c) (Br A u g c) →
        algebraMap ℤ (Br A u g c) n' * s = 0 := by
  classical
  haveI := hfin
  haveI : IsDomain (Localization.Away c) := isDomain_away hc
  set T := Submodule.torsion (Localization.Away c) (Br A u g c) with hT
  haveI : IsNoetherian (Localization.Away c) (Br A u g c) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : Module.Finite (Localization.Away c) T := Module.Finite.iff_fg.2 (IsNoetherian.noetherian T)
  have hTt : Module.IsTorsion (Localization.Away c) T := Submodule.torsion_isTorsion
  obtain ⟨r, hrann, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hTt

  obtain ⟨⟨N, ⟨_, k, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers c) r
  simp only at hr
  have hr0' : r ≠ 0 := nonZeroDivisors.ne_zero hr0
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [map_zero, map_pow, mul_eq_zero] at hr
    rcases hr with h | h
    · exact hr0' h
    · exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c).pow k).ne_zero h
  have hNkill : ∀ t : Br A u g c, t ∈ T → algebraMap ℤ (Br A u g c) N * t = 0 := by
    intro t ht
    have h1 : r • (⟨t, ht⟩ : T) = 0 := Submodule.mem_annihilator.1 hrann ⟨t, ht⟩ Submodule.mem_top
    have h1' : algebraMap (Localization.Away c) (Br A u g c) r * t = 0 := by
      have := congrArg Subtype.val h1
      simp only [Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero] at this
      rw [← Algebra.smul_def]
      exact this
    have hN : algebraMap ℤ (Br A u g c) N = algebraMap (Localization.Away c) (Br A u g c) (algebraMap ℤ _ c ^ k) *
        algebraMap (Localization.Away c) (Br A u g c) r := by
      rw [map_pow] at hr
      rw [← map_mul, mul_comm, hr]
      exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (Br A u g c))
        ((algebraMap (Localization.Away c) (Br A u g c)).comp (algebraMap ℤ (Localization.Away c)))) N
    rw [hN, mul_assoc, h1', mul_zero]

  obtain ⟨e, m, hpm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hN0) p hp.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hNm; exact Int.natAbs_ne_zero.2 hN0 hNm
  have hsign : N.sign = 1 ∨ N.sign = -1 := by
    rcases lt_trichotomy N 0 with h | h | h
    · exact Or.inr (Int.sign_eq_neg_one_of_neg h)
    · exact absurd h hN0
    · exact Or.inl (Int.sign_eq_one_of_pos h)
  refine ⟨N.sign * m, mul_ne_zero (by rcases hsign with h | h <;> simp [h]) (by exact_mod_cast hm0), ?_, ?_⟩
  · intro hdvd
    have : (p : ℤ) ∣ (m : ℤ) := by
      rcases hsign with h1 | h1 <;> rw [h1] at hdvd <;> simpa using hdvd
    exact hpm (Int.natCast_dvd_natCast.1 this)
  · intro s hs
    have hNs := hNkill s hs
    have hNeq : (N : ℤ) = (p : ℤ) ^ e * (N.sign * m) := by
      conv_lhs => rw [← Int.sign_mul_natAbs N, hNm]
      push_cast; ring
    rw [hNeq, map_mul, map_pow, map_natCast] at hNs
    have := smul_eq_zero_of_pow_mul (R := Br A u g c) (M := Br A u g c) (π := (p : Br A u g c))
      (n := algebraMap ℤ (Br A u g c) (N.sign * m)) (fun x hx => hpt x hx) e (t := s) (by simpa [smul_eq_mul] using hNs)
    simpa [smul_eq_mul] using this

theorem noZeroSMulDivisors_of_kills (hcd : c * d ≠ 0)
    (hkill : ∀ s : Br A u g c, s ∈ Submodule.torsion (Localization.Away c) (Br A u g c) →
      algebraMap ℤ (Br A u g c) d * s = 0) :
    Module.IsTorsionFree (Localization.Away (c * d)) (Br A u g (c * d)) := by
  classical
  have hc : c ≠ 0 := left_ne_zero_of_mul hcd
  haveI : IsDomain (Localization.Away c) := isDomain_away hc
  haveI : IsDomain (Localization.Away (c * d)) := isDomain_away hcd
  refine (Module.isTorsionFree_iff_smul_eq_zero).2 (fun r₁ s₁ h => ?_)
  by_cases hr₁ : r₁ = 0
  · exact Or.inl hr₁
  right

  obtain ⟨⟨r₀, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers (algebraMap ℤ (Localization.Away c) d)) r₁
  obtain ⟨⟨s₀, t⟩, hs⟩ :=
    IsLocalization.surj ((Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
      (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g}))) s₁
  obtain ⟨y, hy, hyt⟩ := t.2
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hy
  simp only at hr hs
  rw [← hyt, map_pow] at hs
  have hr₀ : r₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hr
    rcases hr with h | h
    · exact hr₁ h
    · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (c * d))
        (algebraMap ℤ (Localization.Away c) d)).pow m |>.ne_zero (by rw [← map_pow]; exact h)

  set dB : Br A u g c := Ideal.Quotient.mk _ (algebraMap ℤ (Aaway A c) d) with hdB
  have hdB' : dB = algebraMap ℤ (Br A u g c) d :=
    RingHom.congr_fun (Subsingleton.elim ((Ideal.Quotient.mk _).comp (algebraMap ℤ (Aaway A c))) (algebraMap ℤ (Br A u g c))) d
  have h0 : algebraMap (Br A u g c) (Br A u g (c * d)) (algebraMap (Localization.Away c) (Br A u g c) r₀ * s₀) = 0 := by
    set φB := algebraMap (Br A u g c) (Br A u g (c * d)) with hφB
    set φR := algebraMap (Localization.Away (c * d)) (Br A u g (c * d)) with hφR
    set ρ := algebraMap (Localization.Away c) (Localization.Away (c * d)) with hρ
    have e1 : φB (algebraMap (Localization.Away c) (Br A u g c) r₀) = φR (ρ r₀) := by
      rw [hφB, hφR, hρ, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have hmul : φR r₁ * s₁ = 0 := by
      rw [hφR, ← Algebra.smul_def]; exact h
    calc φB (algebraMap (Localization.Away c) (Br A u g c) r₀ * s₀)
        = φR (ρ r₀) * φB s₀ := by rw [RingHom.map_mul φB, e1]
      _ = φR (r₁ * ρ (algebraMap ℤ (Localization.Away c) d ^ m)) * (s₁ * φB (dB ^ n)) := by rw [← hr, ← hs]
      _ = (φR r₁ * s₁) * (φR (ρ (algebraMap ℤ (Localization.Away c) d ^ m)) * φB (dB ^ n)) := by
          rw [RingHom.map_mul φR]; ring
      _ = 0 := by rw [hmul, zero_mul]
  rw [IsLocalization.map_eq_zero_iff ((Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
      (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g})))] at h0
  obtain ⟨w, he⟩ := h0
  obtain ⟨y', hy', hyw⟩ := w.2
  obtain ⟨e, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hy'
  rw [← hyw, map_pow] at he

  have htor : dB ^ e * s₀ ∈ Submodule.torsion (Localization.Away c) (Br A u g c) := by
    refine (Submodule.mem_torsion_iff _).2 ⟨⟨r₀, mem_nonZeroDivisors_of_ne_zero hr₀⟩, ?_⟩
    have hh : algebraMap (Localization.Away c) (Br A u g c) r₀ * (dB ^ e * s₀) = 0 := by
      rw [← mul_assoc, mul_comm _ (dB ^ e), mul_assoc, hdB, ← map_pow]
      exact he
    rw [← Algebra.smul_def] at hh
    exact hh
  have hk := hkill _ htor
  rw [← hdB', ← mul_assoc, ← pow_succ'] at hk

  have hs₀ : algebraMap (Br A u g c) (Br A u g (c * d)) s₀ = 0 := by
    rw [IsLocalization.map_eq_zero_iff ((Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map
      (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g})))]
    refine ⟨⟨_, ⟨_, ⟨e + 1, rfl⟩, rfl⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ (algebraMap ℤ (Aaway A c) d ^ (e + 1)) * s₀ = 0
    rw [map_pow, ← hdB]; exact hk
  have hunit : IsUnit (algebraMap (Br A u g c) (Br A u g (c * d)) (dB ^ n)) := by
    rw [hdB, ← map_pow]
    exact IsLocalization.map_units (Br A u g (c * d)) (⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩⟩ :
      (Submonoid.powers (algebraMap ℤ (Aaway A c) d)).map (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) u) g})))
  rw [hs₀] at hs
  exact (hunit.mul_left_eq_zero).1 hs

theorem flat_of_kills (hcd : c * d ≠ 0)
    (hkill : ∀ s : Br A u g c, s ∈ Submodule.torsion (Localization.Away c) (Br A u g c) →
      algebraMap ℤ (Br A u g c) d * s = 0) :
    Module.Flat (Localization.Away (c * d)) (Br A u g (c * d)) := by
  haveI : IsDomain (Localization.Away (c * d)) := isDomain_away hcd
  haveI : IsDedekindDomain (Localization.Away (c * d)) := inferInstance
  haveI := noZeroSMulDivisors_of_kills hcd hkill
  infer_instance

end torsion

section spread

variable {A c d u g}

private abbrev _root_.LevelBC.pIdeal (p : ℕ) (c : ℤ) : Ideal (Localization.Away c) := Ideal.span {algebraMap ℤ (Localization.Away c) p}

p2m_export "LevelBC" "pIdeal"
theorem exists_etale_int (hc : c ≠ 0) (p : ℕ) [hp : Fact p.Prime] (hpc : ¬ (p : ℤ) ∣ c)
    (hprime : (pIdeal p c).IsPrime)
    [hfin : Module.Finite (Localization.Away c) (Br A u g c)] [hflat : Module.Flat (Localization.Away c) (Br A u g c)]
    (hgen : ∀ (q : Ideal (Br A u g c)) [q.IsPrime], q.comap (algebraMap (Localization.Away c) (Br A u g c)) = ⊥ →
      Algebra.IsUnramifiedAt (Localization.Away c) q)
    (hatp : ∀ (q : Ideal (Br A u g c)) [q.IsPrime], q.comap (algebraMap (Localization.Away c) (Br A u g c)) = pIdeal p c →
      Algebra.IsUnramifiedAt (Localization.Away c) q) :
    ∃ N : ℤ, N ≠ 0 ∧ ¬ (p : ℤ) ∣ N ∧
      Algebra.FormallyEtale (Localization.Away (c * N)) (Br A u g (c * N)) := by
  classical
  haveI : IsDomain (Localization.Away c) := isDomain_away hc
  haveI : Algebra.FinitePresentation (Localization.Away c) (Br A u g c) :=
    (Algebra.FinitePresentation.of_finiteType (R := Localization.Away c) (A := Br A u g c)).mp inferInstance

  have hgen' : ∀ (q : Ideal (Br A u g c)) [q.IsPrime], q.comap (algebraMap (Localization.Away c) (Br A u g c)) = ⊥ →
      Algebra.IsEtaleAt (Localization.Away c) q := fun q _ hq => by
    haveI := hgen q hq
    exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
  have hatp' : ∀ P ∈ ({pIdeal p c} : Finset (Ideal (Localization.Away c))), ∀ (q : Ideal (Br A u g c)) [q.IsPrime],
      q.comap (algebraMap (Localization.Away c) (Br A u g c)) = P → Algebra.IsEtaleAt (Localization.Away c) q := by
    intro P hP q _ hq
    rw [Finset.mem_singleton] at hP
    subst hP
    haveI := hatp q hq
    exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q

  obtain ⟨c', hc'0, hc'p, het⟩ := Algebra.exists_etale_localizationAway_of_forall_isEtaleAt hgen' {pIdeal p c}
    (fun P hP => by rw [Finset.mem_singleton] at hP; subst hP; exact hprime) hatp'
  have hc'p' : c' ∉ pIdeal p c := hc'p _ (Finset.mem_singleton_self _)

  obtain ⟨⟨N, ⟨_, k, rfl⟩⟩, hN⟩ := IsLocalization.surj (Submonoid.powers c) c'
  simp only [map_pow] at hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hN
    exact hN.elim hc'0 (fun h => ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c).pow k).ne_zero h)
  have hNp : ¬ (p : ℤ) ∣ N := by
    intro hdvd
    apply hc'p'
    have hmem : algebraMap ℤ (Localization.Away c) N ∈ pIdeal p c := by
      obtain ⟨m, rfl⟩ := hdvd
      rw [map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← hN] at hmem
    exact (Ideal.IsPrime.mem_or_mem hprime hmem).resolve_right
      (fun h => hc'p' ((Ideal.IsPrime.mem_of_pow_mem hprime k h) |> fun h' => absurd h' (fun h'' =>
        (Ideal.IsPrime.ne_top hprime) ((Ideal.eq_top_iff_one _).2 (by
          have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
          obtain ⟨v, hv⟩ := hu.exists_left_inv
          have := Ideal.mul_mem_left _ v h''; rwa [hv] at this)))))
  have hassocR : Associated c' (algebraMap ℤ (Localization.Away c) N) :=
    ⟨((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c).pow k).unit, by simpa using hN⟩
  refine ⟨N, hN0, hNp, ?_⟩

  haveI : IsDomain (Localization.Away (c * N)) := isDomain_away (mul_ne_zero hc hN0)
  letI := (Localization.awayMap (algebraMap (Localization.Away c) (Br A u g c)) c').toAlgebra
  haveI := het

  haveI : Algebra.FormallyEtale (Localization.Away c) (Localization.Away c') :=
    Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers c')
  have hT := IsScalarTower.of_algebraMap_eq' (R := Localization.Away c) (S := Localization.Away c')
    (A := Localization.Away (algebraMap (Localization.Away c) (Br A u g c) c')) (ringHom_away_ext _ _)
  haveI := hT
  haveI hE1 : Algebra.FormallyEtale (Localization.Away c) (Localization.Away (algebraMap (Localization.Away c) (Br A u g c) c')) :=
    Algebra.FormallyEtale.comp (Localization.Away c) (Localization.Away c') _

  have hsub := submonoid_eq (A := A) (c := c) (d := N) (u := u) (g := g)
  haveI hlocB : IsLocalization.Away (algebraMap (Localization.Away c) (Br A u g c) (algebraMap ℤ (Localization.Away c) N))
      (Br A u g (c * N)) := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (Br A u g c) (Submonoid.powers (algebraMap ℤ (Localization.Away c) N)))
        (Br A u g (c * N)) := by rw [hsub]; exact isLocB A c N u g
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  haveI hlocB' : IsLocalization.Away (algebraMap (Localization.Away c) (Br A u g c) c') (Br A u g (c * N)) :=
    IsLocalization.Away.of_associated (hassocR.map (algebraMap (Localization.Away c) (Br A u g c))).symm
  let e : Localization.Away (algebraMap (Localization.Away c) (Br A u g c) c') ≃ₐ[Br A u g c] Br A u g (c * N) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap (Localization.Away c) (Br A u g c) c')) _ _
  haveI hE2 : Algebra.FormallyEtale (Localization.Away c) (Br A u g (c * N)) :=
    Algebra.FormallyEtale.of_equiv (e.restrictScalars (Localization.Away c))

  have hloc2 : IsLocalization ((Submonoid.powers (algebraMap ℤ (Localization.Away c) N)).map
      (algebraMap (Localization.Away c) (Br A u g c))) (Br A u g (c * N)) := by
    rw [← Algebra.algebraMapSubmonoid, hsub]; exact isLocB A c N u g
  exact Algebra.FormallyEtale.localization_base (R := Localization.Away c)
    (Rₘ := Localization.Away (c * N)) (Sₘ := Br A u g (c * N)) (Submonoid.powers (algebraMap ℤ (Localization.Away c) N))

end spread

end LevelBC
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

namespace LevelPFibre

variable {k : Type*} [Field k]

theorem dvd_of_irreducible_of_root {K : Type*} [Field K] [Algebra k K] {q r : k[X]} (hq : Irreducible q)
    {β : K} (hqβ : aeval β q = 0) (hrβ : aeval β r = 0) : q ∣ r := by
  have hmin : minpoly k β ∣ q := minpoly.dvd k β hqβ
  have hint : IsIntegral k β := ⟨q * C q.leadingCoeff⁻¹, by
    refine ⟨?_, ?_⟩
    · rw [Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀ (leadingCoeff_ne_zero.2 hq.ne_zero)]
    · rw [eval₂_mul, ← aeval_def, hqβ, zero_mul]⟩
  have hassoc : Associated (minpoly k β) q := by
    refine (minpoly.irreducible hint).associated_of_dvd hq hmin
  exact hassoc.symm.dvd.trans (minpoly.dvd k β hrβ)

theorem exists_avoid [PerfectField k] (U : k[X]) (hU : derivative U ≠ 0) :
    ∃ avoid : k[X], avoid ≠ 0 ∧ X ∣ avoid ∧
      ∀ q : k[X], Irreducible q → IsCoprime q avoid →
        q.eval 0 ≠ 0 ∧ (q.comp U).Separable := by
  classical
  let K := AlgebraicClosure k
  let UK : K[X] := U.map (algebraMap k K)
  have hUK : derivative UK ≠ 0 := by
    rw [Polynomial.derivative_map]; exact (Polynomial.map_ne_zero_iff (algebraMap k K).injective).2 hU

  have hfin : {c : K | ∃ x : K, UK.eval x = c ∧ (derivative UK).eval x = 0}.Finite :=
    Polynomial.finite_setOf_criticalValue UK hUK
  let S : Finset K := hfin.toFinset
  let avoid : k[X] := X * ∏ c ∈ S, minpoly k c
  have hint : ∀ c : K, IsIntegral k c := fun c => Algebra.IsIntegral.isIntegral c
  have havoid0 : avoid ≠ 0 :=
    mul_ne_zero X_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ => minpoly.ne_zero (hint c))
  refine ⟨avoid, havoid0, dvd_mul_right _ _, fun q hq hcop => ?_⟩

  have hroot : ∀ β : K, aeval β q = 0 → β ≠ 0 ∧ β ∉ S := by
    intro β hβ
    constructor
    · rintro rfl
      have hX : q ∣ avoid := (dvd_of_irreducible_of_root hq hβ (by simp)).trans (dvd_mul_right X _)
      exact hq.not_isUnit (hcop.isUnit_of_dvd' dvd_rfl hX)
    · intro hβS
      have h1 : q ∣ minpoly k β := dvd_of_irreducible_of_root hq hβ (minpoly.aeval k β)
      have h2 : minpoly k β ∣ avoid := (Finset.dvd_prod_of_mem _ hβS).trans (dvd_mul_left _ _)
      exact hq.not_isUnit (hcop.isUnit_of_dvd' dvd_rfl (h1.trans h2))
  constructor
  ·
    intro h0
    refine (hroot 0 ?_).1 rfl
    rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero, h0, map_zero]
  ·
    rw [← Polynomial.separable_map (algebraMap k K), Polynomial.map_comp]
    have hqK : (q.map (algebraMap k K)).Separable :=
      (PerfectField.separable_iff_squarefree.2 hq.squarefree).map
    have hq0 : q.map (algebraMap k K) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k K).injective).2 hq.ne_zero

    have hsplit := (IsAlgClosed.splits (q.map (algebraMap k K))).eq_prod_roots
    have hnodup : (q.map (algebraMap k K)).roots.Nodup := Polynomial.nodup_roots hqK
    set T : Finset K := (q.map (algebraMap k K)).roots.toFinset with hT
    have hprod : ((q.map (algebraMap k K)).roots.map fun a => X - C a).prod = ∏ a ∈ T, (X - C a) := by
      rw [hT, ← Multiset.toFinset_eq hnodup]; rfl
    rw [hsplit, hprod, mul_comp, C_comp, Polynomial.prod_comp]
    have hfac : ∀ a : K, (X - C a).comp (U.map (algebraMap k K)) = UK - C a := fun a => by
      rw [sub_comp, X_comp, C_comp]
    simp_rw [hfac]

    have hmemT : ∀ a ∈ T, aeval a q = 0 := fun a ha => by
      rw [hT, Multiset.mem_toFinset, mem_roots hq0, IsRoot.def, eval_map, ← aeval_def] at ha
      exact ha
    rw [mul_comm]
    refine (separable_prod' (fun a ha b hb hab => ?_) (fun a ha => ?_)).mul_unit ?_
    ·
      refine ⟨C (b - a)⁻¹, -C (b - a)⁻¹, ?_⟩
      have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      have e' : C (b - a)⁻¹ * (C b - C a) = (1 : K[X]) := by rw [← C_sub, ← C_mul, inv_mul_cancel₀ hba, C_1]
      linear_combination e'
    · refine Polynomial.separable_sub_C_of_forall_eval_derivative UK a (fun x hx hxa => ?_)
      have := (hroot a (hmemT a ha)).2
      apply this
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hxa, hx⟩
    · exact isUnit_C.2 (IsUnit.mk0 _ (leadingCoeff_ne_zero.2 hq0))

end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

namespace LevelPFibre

variable {A : Type*} [CommRing A] {Pu Pz : Ideal A} [Pu.IsPrime] [Pz.IsPrime] {π x : A}

theorem mem_span_of_mul_mem (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x))
    (hxu : x ∉ Pu) {y : A} (h : x * y ∈ Ideal.span {π}) : y ∈ Ideal.span {π} := by
  rw [← hinf] at h ⊢
  refine ⟨(Ideal.IsPrime.mem_or_mem ‹Pu.IsPrime› h.1).resolve_left hxu, ?_⟩
  have h2 : Ideal.Quotient.mk Pz x * Ideal.Quotient.mk Pz y = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact h.2
  show y ∈ Pz
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (hxz.mul_right_eq_zero).1 h2

theorem le_span_sup_span (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x)) :
    Pu ≤ Ideal.span {π} ⊔ Ideal.span {x} := by
  intro y hy
  obtain ⟨w, hw⟩ := hxz.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hz : x * z - 1 ∈ Pz := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self]
  have hprod : (x * z - 1) * y ∈ Ideal.span {π} := by
    rw [← hinf]
    exact ⟨Pu.mul_mem_left _ hy, Pz.mul_mem_right _ hz⟩
  have : y = x * (z * y) - (x * z - 1) * y := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨z * y, by ring⟩))
    (Ideal.mem_sup_left hprod)

theorem pi_mem (hinf : Pu ⊓ Pz = Ideal.span {π}) : π ∈ Pu :=
  (hinf.symm ▸ Ideal.mem_span_singleton_self π : π ∈ Pu ⊓ Pz).1

noncomputable def quotEquiv (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x)) :
    (A ⧸ Ideal.span {π} ⊔ Ideal.span {x}) ≃+* (A ⧸ Pu) ⧸ Ideal.span {Ideal.Quotient.mk Pu x} := by
  refine (Ideal.quotEquivOfEq ?_).trans (DoubleQuot.quotQuotEquivQuotSup Pu (Ideal.span {π} ⊔ Ideal.span {x})).symm
    |>.trans (Ideal.quotEquivOfEq ?_)
  · exact (sup_eq_right.2 (le_span_sup_span hinf hxz)).symm
  · rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Ideal.Quotient.eq_zero_iff_mem.2 (pi_mem hinf), Ideal.span_singleton_zero, bot_sup_eq]

noncomputable def quotEquivOfEquiv {T : Type*} [CommRing T] (hinf : Pu ⊓ Pz = Ideal.span {π})
    (hxz : IsUnit (Ideal.Quotient.mk Pz x)) (e : (A ⧸ Pu) ≃+* T) :
    (A ⧸ Ideal.span {π} ⊔ Ideal.span {x}) ≃+* T ⧸ Ideal.span {e (Ideal.Quotient.mk Pu x)} :=
  (quotEquiv hinf hxz).trans (Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl))

end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

namespace LevelPFibre

theorem etale_quotient_span_of_separable (k : Type u) [Field k] (h : k[X]) (hsep : h.Separable) :
    Algebra.Etale k (k[X] ⧸ Ideal.span {h}) := by
  have hunr : ∀ (P : Ideal k[X]) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] k[X]) →
      Algebra.IsUnramifiedAt k[X] P := fun P _ _ _ =>
    Algebra.FormallyUnramified.of_isLocalization (M := P.primeCompl)
  have H := IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt (k := k) k[X] h hsep hunr
  have heq : Ideal.map (algebraMap k[X] k[X]) (Ideal.span {h}) = Ideal.span {h} := Ideal.map_id _
  exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlgOfEq k heq)

end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

namespace LevelPFibre

variable {A : Type*} [CommRing A]

abbrev Aaway (A : Type*) [CommRing A] (r : ℤ) : Type _ := Localization.Away (algebraMap ℤ A r)

private abbrev _root_.LevelPFibre.Br (A : Type*) [CommRing A] (u : A) (g : ℤ[X]) (r : ℤ) : Type _ :=
  Aaway A r ⧸ Ideal.span {aeval (algebraMap A (Aaway A r) u) g}

p2m_export "LevelPFibre" "Br"
theorem aeval_algebraMap_eq (u : A) (g : ℤ[X]) (r : ℤ) :
    aeval (algebraMap A (Aaway A r) u) g = algebraMap A (Aaway A r) (aeval u g) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  exact congrArg (fun f : ℤ →+* Aaway A r => eval₂ f (algebraMap A (Aaway A r) u) g) (Subsingleton.elim _ _)

theorem eq_zero_of_pi_mul_eq_zero [IsDomain A] (u : A) (g : ℤ[X]) {π : A} (hπ : π ≠ 0)
    (hnzd : ∀ y : A, aeval u g * y ∈ Ideal.span {π} → y ∈ Ideal.span {π})
    {c : ℤ} (hc : algebraMap ℤ A c ≠ 0) (s : Br A u g c)
    (hs : algebraMap A (Br A u g c) π * s = 0) : s = 0 := by
  classical
  set x : A := aeval u g with hx
  set φ : A →+* Aaway A c := algebraMap A (Aaway A c) with hφ
  haveI : IsDomain (Aaway A c) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
  have hinj : Function.Injective φ :=
    IsLocalization.injective (Aaway A c) (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
  have hunit : ∀ k : ℕ, IsUnit (φ (algebraMap ℤ A c ^ k)) := fun k => by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap ℤ A c)).pow k
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s

  have hs1 : φ π * s ∈ Ideal.span {φ x} := by
    rw [← aeval_algebraMap_eq, ← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hs1

  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hs'⟩ := IsLocalization.surj (Submonoid.powers (algebraMap ℤ A c)) s
  obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, ht'⟩ := IsLocalization.surj (Submonoid.powers (algebraMap ℤ A c)) t
  simp only at hs' ht'
  rw [← hφ] at hs' ht'

  have key : π * a * algebraMap ℤ A c ^ m = x * b * algebraMap ℤ A c ^ n := by
    apply hinj
    have := congrArg (fun z => z * φ (algebraMap ℤ A c ^ n) * φ (algebraMap ℤ A c ^ m)) ht
    beta_reduce at this

    simp only [map_mul]
    calc φ π * φ a * φ (algebraMap ℤ A c ^ m)
        = φ π * (s * φ (algebraMap ℤ A c ^ n)) * φ (algebraMap ℤ A c ^ m) := by rw [hs']
      _ = t * φ x * φ (algebraMap ℤ A c ^ n) * φ (algebraMap ℤ A c ^ m) := by rw [this]; ring
      _ = φ x * (t * φ (algebraMap ℤ A c ^ m)) * φ (algebraMap ℤ A c ^ n) := by ring
      _ = φ x * φ b * φ (algebraMap ℤ A c ^ n) := by rw [ht']

  have hb : b * algebraMap ℤ A c ^ n ∈ Ideal.span {π} :=
    hnzd _ (Ideal.mem_span_singleton'.2 ⟨a * algebraMap ℤ A c ^ m, by rw [← mul_assoc, ← key]; ring⟩)
  obtain ⟨b'', hb''⟩ := Ideal.mem_span_singleton'.1 hb

  have key' : a * algebraMap ℤ A c ^ m = x * b'' := by
    have h1 : π * (a * algebraMap ℤ A c ^ m) = π * (x * b'') := by
      rw [← mul_assoc, key, mul_assoc, ← hb'']; ring
    exact mul_left_cancel₀ hπ h1

  rw [Ideal.Quotient.eq_zero_iff_mem, aeval_algebraMap_eq]
  obtain ⟨un, hun⟩ := hunit n
  obtain ⟨um, hum⟩ := hunit m
  refine Ideal.mem_span_singleton'.2 ⟨φ b'' * ↑um⁻¹ * ↑un⁻¹, ?_⟩
  have hs'' : s = φ a * ↑un⁻¹ := by
    rw [← hs', ← hun, mul_assoc, Units.mul_inv, mul_one]
  rw [hs'']
  have : φ a = φ x * φ b'' * ↑um⁻¹ := by
    rw [← map_mul, ← key', map_mul, ← hum, mul_assoc, Units.mul_inv, mul_one]
  rw [this]; ring

end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

namespace LevelPFibre

theorem isLocalHom_of_field {K L : Type*} [Field K] [CommRing L] [Nontrivial L] (f : K →+* L) : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · rw [map_zero] at ha; exact (not_isUnit_zero ha).elim
    · exact isUnit_iff_ne_zero.2 h⟩

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.EssFiniteType ℤ R]

set_option maxHeartbeats 3200000 in

theorem isUnramifiedAt_of_fibre (p : ℕ) [Fact p.Prime] (𝔭 : Ideal R) [𝔭.IsMaximal] (hp : (p : R) ∈ 𝔭)
    (hκ : Finite (R ⧸ 𝔭))
    (hF : Algebra.FormallyUnramified ℤ (S ⧸ 𝔭.map (algebraMap R S)))
    (q : Ideal S) [q.IsPrime] [q.LiesOver 𝔭] : Algebra.IsUnramifiedAt R q := by
  classical
  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 q
  have hess : Algebra.EssFiniteType R S := inferInstance
  rw [Algebra.isUnramifiedAt_iff_map_eq R 𝔭 q]
  constructor
  ·
    haveI : Finite 𝔭.ResidueField :=
      Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝔭).surjective
    haveI : PerfectField 𝔭.ResidueField := PerfectField.ofFinite
    haveI : Module.Finite 𝔭.ResidueField q.ResidueField := inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  ·
    set I : Ideal S := 𝔭.map (algebraMap R S) with hI

    have hJI : 𝔭.map (algebraMap R (Localization.AtPrime q)) = I.map (algebraMap S (Localization.AtPrime q)) := by
      rw [hI, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [hJI]
    set J : Ideal (Localization.AtPrime q) := I.map (algebraMap S (Localization.AtPrime q)) with hJ
    haveI : (maximalIdeal (Localization.AtPrime q)).LiesOver 𝔭 := Ideal.LiesOver.trans _ q 𝔭
    have hJle : J ≤ maximalIdeal (Localization.AtPrime q) := by
      rw [← hJI, Ideal.map_le_iff_le_comap]
      exact le_of_eq (Ideal.LiesOver.over (p := 𝔭) (P := maximalIdeal (Localization.AtPrime q)))
    have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJle

    haveI : Nontrivial (Localization.AtPrime q ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
    haveI : IsLocalRing (Localization.AtPrime q ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective

    haveI : Algebra.FormallyUnramified (S ⧸ I) (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_isLocalization (Algebra.algebraMapSubmonoid (S ⧸ I) q.primeCompl)
    have hT1 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := S ⧸ I) (A := Localization.AtPrime q ⧸ J)
      (Subsingleton.elim _ _)
    haveI := hT1
    haveI : Algebra.FormallyUnramified ℤ (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.comp ℤ (S ⧸ I) _

    have hpJ : (p : Localization.AtPrime q ⧸ J) = 0 := by
      rw [← map_natCast (algebraMap S (Localization.AtPrime q ⧸ J)), ← map_natCast (algebraMap R S),
        IsScalarTower.algebraMap_apply S (Localization.AtPrime q) (Localization.AtPrime q ⧸ J),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJ]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp)
    haveI : CharP (Localization.AtPrime q ⧸ J) p := by
      have hdvd : ringChar (Localization.AtPrime q ⧸ J) ∣ p := (ringChar.spec _ p).1 hpJ
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd h1 (CharP.ringChar_ne_one)
      · exact hp' ▸ ringChar.charP _
    letI : Algebra (ZMod p) (Localization.AtPrime q ⧸ J) := ZMod.algebra _ p
    haveI : IsLocalHom (algebraMap (ZMod p) (Localization.AtPrime q ⧸ J)) := isLocalHom_of_field _
    have hT2 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := Localization.AtPrime q ⧸ J)
      (Subsingleton.elim _ _)
    haveI := hT2
    haveI : Algebra.FormallyUnramified (ZMod p) (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_restrictScalars ℤ (ZMod p) _
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime q ⧸ J) := by
      have : Algebra.EssFiniteType ℤ S := Algebra.EssFiniteType.comp ℤ R S
      have : Algebra.EssFiniteType ℤ (Localization.AtPrime q) := Algebra.EssFiniteType.comp ℤ S _
      exact Algebra.EssFiniteType.comp ℤ (Localization.AtPrime q) _
    haveI : Algebra.EssFiniteType (ZMod p) (Localization.AtPrime q ⧸ J) := Algebra.EssFiniteType.of_comp ℤ (ZMod p) _
    have hmax : maximalIdeal (Localization.AtPrime q ⧸ J) = ⊥ := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := ZMod p) (S := Localization.AtPrime q ⧸ J),
        IsLocalRing.maximalIdeal_eq_bot (R := ZMod p), Ideal.map_bot]

    refine le_antisymm hJle ?_
    have hne : (maximalIdeal (Localization.AtPrime q)).map (Ideal.Quotient.mk J) ≠ ⊤ := by
      rw [Ne, Ideal.map_eq_top_iff_of_ker_le (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact hJle)
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)]
      exact (maximalIdeal.isMaximal _).ne_top
    have hle : (maximalIdeal (Localization.AtPrime q)).map (Ideal.Quotient.mk J) ≤ ⊥ :=
      hmax ▸ IsLocalRing.le_maximalIdeal hne
    intro z hz
    have hz' : Ideal.Quotient.mk J z ∈ (⊥ : Ideal (Localization.AtPrime q ⧸ J)) := hle (Ideal.mem_map_of_mem _ hz)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz'
    exact hz'

end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

namespace LevelPFibre

section base
variable (p : ℕ) [Fact p.Prime] (c : ℤ)

private abbrev _root_.LevelPFibre.pIdeal : Ideal (Localization.Away c) := Ideal.span {algebraMap ℤ (Localization.Away c) p}

p2m_export "LevelPFibre" "pIdeal"
theorem not_isUnit_away (hc : ¬ (p : ℤ) ∣ c) : ¬ IsUnit (algebraMap ℤ (Localization.Away c) p) := by
  intro h
  rw [IsLocalization.Away.algebraMap_isUnit_iff c] at h
  obtain ⟨n, hn⟩ := h
  exact hc (Int.Prime.dvd_pow' (Fact.out : p.Prime) hn)

theorem pIdeal_ne_top (hc : ¬ (p : ℤ) ∣ c) : pIdeal p c ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_away p c hc

theorem natCast_mem_pIdeal : (p : Localization.Away c) ∈ pIdeal p c := by
  have : (p : Localization.Away c) = algebraMap ℤ (Localization.Away c) p := by simp
  rw [this]; exact Ideal.mem_span_singleton_self _

scoped instance charP_quotient_pIdeal [hc : Fact (¬ (p : ℤ) ∣ c)] : CharP (Localization.Away c ⧸ pIdeal p c) p := by
  have hp0 : (p : Localization.Away c ⧸ pIdeal p c) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_mem_pIdeal p c
  haveI : Nontrivial (Localization.Away c ⧸ pIdeal p c) := Ideal.Quotient.nontrivial_iff.2 (pIdeal_ne_top p c hc.out)
  have hdvd : ringChar (Localization.Away c ⧸ pIdeal p c) ∣ p := (ringChar.spec (Localization.Away c ⧸ pIdeal p c) p).1 hp0
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
  · exact absurd h1 CharP.ringChar_ne_one
  · have := ringChar.charP (Localization.Away c ⧸ pIdeal p c)
    rwa [hp'] at this

theorem zmod_surjective [hc : Fact (¬ (p : ℤ) ∣ c)] :
    Function.Surjective (ZMod.castHom (dvd_refl p) (Localization.Away c ⧸ pIdeal p c)) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers c) z
  simp only [map_pow] at hz

  have hcu : IsUnit ((c : ZMod p)) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hc.out
  obtain ⟨cu, hcu'⟩ := hcu
  refine ⟨(a : ZMod p) * ↑(cu⁻¹ ^ n), ?_⟩

  have hcn : IsUnit (Ideal.Quotient.mk (pIdeal p c) (algebraMap ℤ (Localization.Away c) c) ^ n) :=
    ((IsLocalization.Away.algebraMap_isUnit c).map _).pow n
  refine (hcn.mul_left_inj).1 ?_
  rw [← map_pow, ← map_mul, hz]
  have h1 : (ZMod.castHom (dvd_refl p) (Localization.Away c ⧸ pIdeal p c)) (a : ZMod p) =
      Ideal.Quotient.mk (pIdeal p c) (algebraMap ℤ _ a) := by
    rw [map_intCast]; simp
  have h2 : (ZMod.castHom (dvd_refl p) (Localization.Away c ⧸ pIdeal p c)) (cu : ZMod p) =
      Ideal.Quotient.mk (pIdeal p c) (algebraMap ℤ _ c) := by
    rw [hcu', map_intCast]; simp
  have key : ((a : ZMod p) * ↑(cu⁻¹ ^ n)) * (cu : ZMod p) ^ n = a := by
    rw [mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, mul_one]
  rw [map_pow, ← h2, ← map_pow, ← map_mul, key, h1]

theorem isMaximal_pIdeal [hc : Fact (¬ (p : ℤ) ∣ c)] : (pIdeal p c).IsMaximal := by
  haveI : Nontrivial (Localization.Away c ⧸ pIdeal p c) := Ideal.Quotient.nontrivial_iff.2 (pIdeal_ne_top p c hc.out)
  have hsurj := zmod_surjective p c
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (Localization.Away c ⧸ pIdeal p c)) := RingHom.injective _
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField (Field.toIsField (ZMod p)) (RingEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm.toMulEquiv

theorem finite_quotient_pIdeal [hc : Fact (¬ (p : ℤ) ∣ c)] : Finite (Localization.Away c ⧸ pIdeal p c) :=
  Finite.of_surjective _ (zmod_surjective p c)

end base
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

theorem formallyUnramified_int_congr {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.FormallyUnramified ℤ X _ _ i₁) : @Algebra.FormallyUnramified ℤ X _ _ i₂ := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem formallyUnramified_int_of_ringEquiv {X Y : Type*} [CommRing X] [CommRing Y] {iX : Algebra ℤ X} {iY : Algebra ℤ Y}
    (e : X ≃+* Y) (h : @Algebra.FormallyUnramified ℤ X _ _ iX) : @Algebra.FormallyUnramified ℤ Y _ _ iY := by
  have h' : @Algebra.FormallyUnramified ℤ X _ _ (Ring.toIntAlgebra X) := formallyUnramified_int_congr _ _ h
  refine formallyUnramified_int_congr (Ring.toIntAlgebra Y) iY ?_
  exact @Algebra.FormallyUnramified.of_equiv ℤ _ X Y _ (Ring.toIntAlgebra X) _ (Ring.toIntAlgebra Y) h'
    (@AlgEquiv.ofRingEquiv ℤ X Y _ _ _ (Ring.toIntAlgebra X) (Ring.toIntAlgebra Y) e (fun n => by simp))

theorem formallyUnramified_int_of_zmod (p : ℕ) [Fact p.Prime] (T : Type*) [CommRing T] [Algebra (ZMod p) T]
    [Algebra.FormallyUnramified (ZMod p) T] {iT : Algebra ℤ T} : @Algebra.FormallyUnramified ℤ T _ _ iT := by
  haveI : Algebra.FormallyUnramified ℤ (ZMod p) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod p)) (ZMod.intCast_surjective)
  have hT := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := T) (Subsingleton.elim _ _)
  haveI := hT
  exact formallyUnramified_int_congr _ _ (Algebra.FormallyUnramified.comp ℤ (ZMod p) T)

section fibre

variable {A : Type} [CommRing A] (p : ℕ) [Fact p.Prime] {Pu Pz : Ideal A} [Pu.IsPrime] [Pz.IsPrime]
  (u : A) (g : ℤ[X]) (c : ℤ) [hc : Fact (¬ (p : ℤ) ∣ c)]

noncomputable scoped instance algAway (r : ℤ) : Algebra (Localization.Away r) (Aaway A r) :=
  (Localization.awayMap (algebraMap ℤ A) r).toAlgebra
noncomputable scoped instance algAwayBr (r : ℤ) : Algebra (Localization.Away r) (Br A u g r) := Ideal.Quotient.algebra _

abbrev Kid (A : Type) [CommRing A] (p : ℕ) (u : A) (g : ℤ[X]) : Ideal A := Ideal.span {(p : A)} ⊔ Ideal.span {aeval u g}

include hc in

theorem isUnit_algebraMap_c_quot : IsUnit (algebraMap ℤ (A ⧸ Kid A p u g) c) := by
  have hp0 : (p : A ⧸ Kid A p u g) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

  have hcop : IsCoprime (c : ℤ) p :=
    ((Nat.prime_iff_prime_int.1 Fact.out).irreducible.coprime_iff_not_dvd.2 hc.out).symm
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨⟨algebraMap ℤ _ c, algebraMap ℤ _ a, ?_, ?_⟩, rfl⟩
  · have := congrArg (algebraMap ℤ (A ⧸ Kid A p u g)) hab
    rw [map_add, map_mul, map_mul, map_one, map_natCast, hp0, mul_zero, add_zero] at this
    rw [mul_comm]; exact this
  · have := congrArg (algebraMap ℤ (A ⧸ Kid A p u g)) hab
    rw [map_add, map_mul, map_mul, map_one, map_natCast, hp0, mul_zero, add_zero] at this
    exact this

end fibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC"

end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre"

namespace LevelPFibre
section fibre2

variable {A : Type} [CommRing A] (p : ℕ) [Fact p.Prime] {Pu Pz : Ideal A} [Pu.IsPrime] [Pz.IsPrime]
  (u : A) (g : ℤ[X]) (c : ℤ) [hc : Fact (¬ (p : ℤ) ∣ c)]

noncomputable def quotEquivAwayQuot :
    (A ⧸ Kid A p u g) ≃ₐ[A ⧸ Kid A p u g] (Aaway A c ⧸ (Kid A p u g).map (algebraMap A (Aaway A c))) :=
  IsLocalization.atUnits (A ⧸ Kid A p u g)
    (Algebra.algebraMapSubmonoid (A ⧸ Kid A p u g) (Submonoid.powers (algebraMap ℤ A c)))
    (by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      show IsUnit (algebraMap A (A ⧸ Kid A p u g) (algebraMap ℤ A c ^ n))
      rw [map_pow, ← IsScalarTower.algebraMap_apply]
      · exact (isUnit_algebraMap_c_quot p u g c).pow n)

noncomputable def fibreEquiv :
    (Br A u g c ⧸ (pIdeal p c).map (algebraMap (Localization.Away c) (Br A u g c))) ≃+*
      (Aaway A c ⧸ (Kid A p u g).map (algebraMap A (Aaway A c))) := by
  refine (Ideal.quotEquivOfEq ?_).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {aeval (algebraMap A (Aaway A c) u) g})
      (Ideal.span {algebraMap ℤ (Aaway A c) p})).trans (Ideal.quotEquivOfEq ?_))
  ·
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    exact RingHom.congr_fun (Subsingleton.elim ((algebraMap (Localization.Away c) (Br A u g c)).comp
      (algebraMap ℤ (Localization.Away c))) ((Ideal.Quotient.mk _).comp (algebraMap ℤ (Aaway A c)))) p
  · rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, sup_comm,
      aeval_algebraMap_eq, map_natCast]
    congr 2
    simp

theorem formallyUnramified_int_fibre (hinf : Pu ⊓ Pz = Ideal.span {(p : A)})
    (hxz : IsUnit (Ideal.Quotient.mk Pz (aeval u g))) (e : (A ⧸ Pu) ≃+* (ZMod p)[X])
    (hsep : (e (Ideal.Quotient.mk Pu (aeval u g))).Separable) :
    Algebra.FormallyUnramified ℤ (Br A u g c ⧸ (pIdeal p c).map (algebraMap (Localization.Away c) (Br A u g c))) := by

  have e1 : (A ⧸ Kid A p u g) ≃+* (ZMod p)[X] ⧸ Ideal.span {e (Ideal.Quotient.mk Pu (aeval u g))} :=
    quotEquivOfEquiv hinf hxz e
  haveI : Algebra.Etale (ZMod p) ((ZMod p)[X] ⧸ Ideal.span {e (Ideal.Quotient.mk Pu (aeval u g))}) :=
    etale_quotient_span_of_separable (ZMod p) _ hsep
  have h1 : Algebra.FormallyUnramified ℤ ((ZMod p)[X] ⧸ Ideal.span {e (Ideal.Quotient.mk Pu (aeval u g))}) :=
    formallyUnramified_int_of_zmod p ((ZMod p)[X] ⧸ Ideal.span {e (Ideal.Quotient.mk Pu (aeval u g))})
  have h2 : Algebra.FormallyUnramified ℤ (A ⧸ Kid A p u g) := formallyUnramified_int_of_ringEquiv e1.symm h1

  have h3 : Algebra.FormallyUnramified ℤ (Aaway A c ⧸ (Kid A p u g).map (algebraMap A (Aaway A c))) :=
    formallyUnramified_int_of_ringEquiv (quotEquivAwayQuot p u g c).toRingEquiv h2

  exact formallyUnramified_int_of_ringEquiv (fibreEquiv p u g c).symm h3

end fibre2
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre"
end LevelPFibre
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre"

namespace LevelPGen

variable {A : Type} [CommRing A] [IsDomain A] [CharZero A]

abbrev Aaway (A : Type) [CommRing A] (r : ℤ) : Type := Localization.Away (algebraMap ℤ A r)
private abbrev _root_.LevelPGen.Br (A : Type) [CommRing A] (u : A) (g : ℤ[X]) (r : ℤ) : Type :=
  Aaway A r ⧸ Ideal.span {aeval (algebraMap A (Aaway A r) u) g}
p2m_export "LevelPGen" "Br"
noncomputable scoped instance algAway (r : ℤ) : Algebra (Localization.Away r) (Aaway A r) :=
  (Localization.awayMap (algebraMap ℤ A) r).toAlgebra
noncomputable scoped instance algAwayBr (u : A) (g : ℤ[X]) (r : ℤ) : Algebra (Localization.Away r) (Br A u g r) :=
  Ideal.Quotient.algebra _

theorem aeval_algebraMap_eq (u : A) (g : ℤ[X]) (r : ℤ) :
    aeval (algebraMap A (Aaway A r) u) g = algebraMap A (Aaway A r) (aeval u g) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  exact congrArg (fun f : ℤ →+* Aaway A r => eval₂ f (algebraMap A (Aaway A r) u) g) (Subsingleton.elim _ _)

theorem ringHom_away_ext {r : ℤ} {X : Type*} [CommRing X] (f₁ f₂ : Localization.Away r →+* X) : f₁ = f₂ :=
  IsLocalization.ringHom_ext (Submonoid.powers r) (Subsingleton.elim _ _)

theorem dvd_of_irreducible_of_root {k K : Type*} [Field k] [Field K] [Algebra k K] {q r : k[X]} (hq : Irreducible q)
    {β : K} (hqβ : aeval β q = 0) (hrβ : aeval β r = 0) : q ∣ r := by
  have hmin : minpoly k β ∣ q := minpoly.dvd k β hqβ
  have hint : IsIntegral k β := ⟨q * C q.leadingCoeff⁻¹, by
    refine ⟨?_, ?_⟩
    · rw [Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀ (leadingCoeff_ne_zero.2 hq.ne_zero)]
    · rw [eval₂_mul, ← aeval_def, hqβ, zero_mul]⟩
  exact ((minpoly.irreducible hint).associated_of_dvd hq hmin).symm.dvd.trans (minpoly.dvd k β hrβ)

theorem aeval_notMem_of_not_dvd (v : A) (g c₀ : ℤ[X]) (hg : g.Monic) (hirr : Irreducible (g.map (Int.castRingHom ℚ)))
    (hndvd : ¬ g ∣ c₀) (P : Ideal A) [P.IsPrime] (hP : P.comap (algebraMap ℤ A) = ⊥) (hgP : aeval v g ∈ P) :
    aeval v c₀ ∉ P := by
  intro hc

  let D := A ⧸ P
  let L := FractionRing (A ⧸ P)
  haveI : CharZero (A ⧸ P) := by
    refine charZero_of_inj_zero (fun n hn => ?_)
    have : (n : ℤ) ∈ P.comap (algebraMap ℤ A) := by
      rw [Ideal.mem_comap, map_natCast, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn
    rw [hP, Ideal.mem_bot] at this
    exact_mod_cast this
  haveI : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (A ⧸ P) L)
  letI : Algebra ℚ L := DivisionRing.toRatAlgebra
  let β : L := algebraMap (A ⧸ P) L (Ideal.Quotient.mk P v)
  have hroot : ∀ f : ℤ[X], aeval v f ∈ P → aeval β (f.map (Int.castRingHom ℚ)) = 0 := by
    intro f hf
    have hT := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := L) (Subsingleton.elim _ _)
    haveI := hT
    have e1 : aeval β (f.map (Int.castRingHom ℚ)) = aeval β f := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]
    have e2 : aeval β f = algebraMap (A ⧸ P) L (aeval (Ideal.Quotient.mk P v) f) := aeval_algebraMap_apply L _ f
    have e3 : aeval (Ideal.Quotient.mk P v) f = Ideal.Quotient.mk P (aeval v f) := by
      rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply]
    rw [e1, e2, e3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hdvd : g.map (Int.castRingHom ℚ) ∣ c₀.map (Int.castRingHom ℚ) :=
    dvd_of_irreducible_of_root hirr (hroot g hgP) (hroot c₀ hc)
  rw [Polynomial.map_dvd_map (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int hg] at hdvd
  exact hndvd hdvd

theorem formallyUnramified_of_surjective' {R X Y : Type*} [CommRing R] [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y]
    (f : X →+* Y) (hf : Function.Surjective f) (hcomm : f.comp (algebraMap R X) = algebraMap R Y)
    [Algebra.FormallyUnramified R X] : Algebra.FormallyUnramified R Y :=
  Algebra.FormallyUnramified.of_surjective ({ f with commutes' := fun r => RingHom.congr_fun hcomm r } : X →ₐ[R] Y) hf

section main
variable (v : A) (g c₀ : ℤ[X]) (c : ℤ)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem isUnramifiedAt_of_comap_eq_bot (hc : c ≠ 0) (hg : g.Monic) (hirr : Irreducible (g.map (Int.castRingHom ℚ)))
    (hndvd : ¬ g ∣ c₀)
    (hunr : letI : Algebra ℤ[X] A := (aeval v).toRingHom.toAlgebra
      ∀ (P : Ideal A) [P.IsPrime], P.comap (algebraMap ℤ A) = ⊥ → aeval v c₀ ∉ P → Algebra.IsUnramifiedAt ℤ[X] P)
    (q : Ideal (Br A v g c)) [q.IsPrime] (hq : q.comap (algebraMap (Localization.Away c) (Br A v g c)) = ⊥) :
    Algebra.IsUnramifiedAt (Localization.Away c) q := by
  classical
  letI iZX : Algebra ℤ[X] A := (aeval v).toRingHom.toAlgebra

  let f : A →+* Br A v g c := (Ideal.Quotient.mk _).comp (algebraMap A (Aaway A c))
  let P : Ideal A := q.comap f
  haveI : P.IsPrime := Ideal.comap_isPrime f q
  have hcA : algebraMap ℤ A c ≠ 0 := fun h => hc (by
    have : Function.Injective (algebraMap ℤ A) := (algebraMap ℤ A).injective_int; exact this (by rw [h, map_zero]))
  haveI : IsDomain (Aaway A c) := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hcA)

  have hPZ : P.comap (algebraMap ℤ A) = ⊥ := by
    refine le_bot_iff.1 (fun n hn => ?_)
    rw [Ideal.mem_comap, Ideal.mem_comap] at hn
    have h1 : f (algebraMap ℤ A n) = algebraMap (Localization.Away c) (Br A v g c) (algebraMap ℤ _ n) :=
      RingHom.congr_fun (Subsingleton.elim (f.comp (algebraMap ℤ A))
        ((algebraMap (Localization.Away c) (Br A v g c)).comp (algebraMap ℤ (Localization.Away c)))) n
    rw [h1, ← Ideal.mem_comap, hq, Ideal.mem_bot] at hn
    have : Function.Injective (algebraMap ℤ (Localization.Away c)) :=
      IsLocalization.injective (Localization.Away c) (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
    exact Ideal.mem_bot.2 (this (by rw [hn, map_zero]))

  have hgP : aeval v g ∈ P := by
    show f (aeval v g) ∈ q
    have : f (aeval v g) = 0 := by
      show Ideal.Quotient.mk _ (algebraMap A (Aaway A c) (aeval v g)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← aeval_algebraMap_eq]; exact Ideal.mem_span_singleton_self _
    rw [this]; exact q.zero_mem

  have hcP : aeval v c₀ ∉ P := aeval_notMem_of_not_dvd v g c₀ hg hirr hndvd P hPZ hgP
  have hUP : Algebra.IsUnramifiedAt ℤ[X] P := hunr P hPZ hcP

  have hPq : P = q.comap f := rfl
  let ψ : Localization.AtPrime P →+* Localization.AtPrime q := Localization.localRingHom P q f hPq
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨s, t⟩, hz⟩ := IsLocalization.surj q.primeCompl z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective (t : Br A v g c)
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap ℤ A c)) s
    obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, ht⟩ := IsLocalization.surj (Submonoid.powers (algebraMap ℤ A c)) t'
    simp only at hs ht hz

    have hf : ∀ x : A, f x = Ideal.Quotient.mk _ (algebraMap A (Aaway A c) x) := fun x => rfl
    have hcP' : algebraMap ℤ A c ∉ P := fun h => by
      have : (c : ℤ) ∈ P.comap (algebraMap ℤ A) := h
      rw [hPZ, Ideal.mem_bot] at this; exact hc this
    have hbP : b ∉ P := by
      intro hb
      apply t.2
      show (t : Br A v g c) ∈ q
      have hb' : f b ∈ q := hb
      rw [← ht']
      have e1 : Ideal.Quotient.mk _ t' * f (algebraMap ℤ A c ^ m) = f b := by
        show Ideal.Quotient.mk _ t' * Ideal.Quotient.mk _ (algebraMap A _ (algebraMap ℤ A c ^ m)) = Ideal.Quotient.mk _ (algebraMap A _ b)
        rw [← map_mul, ht]
      have hu : IsUnit (f (algebraMap ℤ A c ^ m)) := by
        rw [map_pow, hf]
        exact ((IsLocalization.Away.algebraMap_isUnit (S := Aaway A c) (algebraMap ℤ A c)).map
          (Ideal.Quotient.mk (Ideal.span {aeval (algebraMap A (Aaway A c) v) g}))).pow m
      have := q.mul_mem_right (↑hu.unit⁻¹ : Br A v g c) hb'
      rwa [← e1, mul_assoc, IsUnit.mul_val_inv, mul_one] at this
    have hden : b * algebraMap ℤ A c ^ n ∉ P := fun h =>
      (Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h).elim hbP (fun h' => hcP' (Ideal.IsPrime.mem_of_pow_mem ‹_› n h'))
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) (a * algebraMap ℤ A c ^ m)
      (⟨b * algebraMap ℤ A c ^ n, hden⟩ : P.primeCompl), ?_⟩

    rw [Localization.localRingHom_mk', eq_comm, IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk]
    have e2 : f (b * algebraMap ℤ A c ^ n) = (t : Br A v g c) * f (algebraMap ℤ A c ^ m) * f (algebraMap ℤ A c ^ n) := by
      rw [map_mul, ← ht', hf b, ← ht, map_mul, hf]; rfl
    have e3 : f (a * algebraMap ℤ A c ^ m) = Ideal.Quotient.mk _ s * f (algebraMap ℤ A c ^ n) * f (algebraMap ℤ A c ^ m) := by
      rw [map_mul, hf a, ← hs, map_mul, hf, hf]
    rw [e2, e3, map_mul, map_mul, map_mul, map_mul, ← hz]
    ring

  have hX : algebraMap ℤ[X] A X = v := by
    show (aeval v).toRingHom X = v
    simp
  have halgS : algebraMap ℤ[X] (Localization.AtPrime q) =
      (algebraMap (Br A v g c) (Localization.AtPrime q)).comp (f.comp (algebraMap ℤ[X] A)) := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · exact RingHom.congr_fun (Subsingleton.elim ((algebraMap ℤ[X] (Localization.AtPrime q)).comp C)
        (((algebraMap (Br A v g c) (Localization.AtPrime q)).comp (f.comp (algebraMap ℤ[X] A))).comp C)) n
    · rw [IsScalarTower.algebraMap_apply ℤ[X] (Br A v g c) (Localization.AtPrime q),
        IsScalarTower.algebraMap_apply ℤ[X] (Aaway A c) (Br A v g c),
        IsScalarTower.algebraMap_apply ℤ[X] A (Aaway A c)]
      rfl
  have hcomm : ψ.comp (algebraMap ℤ[X] (Localization.AtPrime P)) = algebraMap ℤ[X] (Localization.AtPrime q) := by
    rw [halgS, IsScalarTower.algebraMap_eq ℤ[X] A (Localization.AtPrime P)]
    refine RingHom.ext (fun r => ?_)
    simp only [RingHom.comp_apply]
    exact Localization.localRingHom_to_map P q f hPq _
  haveI hU1 : Algebra.FormallyUnramified ℤ[X] (Localization.AtPrime q) :=
    formallyUnramified_of_surjective' ψ hψ hcomm

  have hunitZ : ∀ y : nonZeroDivisors ℤ, IsUnit (algebraMap ℤ (Localization.AtPrime q) y) := by
    intro y
    have hy : (y : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    have h1 : algebraMap ℤ (Localization.AtPrime q) y = algebraMap (Br A v g c) (Localization.AtPrime q)
        (algebraMap (Localization.Away c) (Br A v g c) (algebraMap ℤ (Localization.Away c) y)) :=
      RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (Localization.AtPrime q))
        (((algebraMap (Br A v g c) (Localization.AtPrime q)).comp (algebraMap (Localization.Away c) (Br A v g c))).comp
          (algebraMap ℤ (Localization.Away c)))) y
    rw [h1]
    refine IsLocalization.map_units (Localization.AtPrime q) (⟨_, ?_⟩ : q.primeCompl)
    intro hmem
    have : algebraMap ℤ (Localization.Away c) y ∈ q.comap (algebraMap (Localization.Away c) (Br A v g c)) := hmem
    rw [hq, Ideal.mem_bot] at this
    exact hy (IsLocalization.injective (Localization.Away c) (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
      (by rw [this, map_zero]))
  let i : ℚ →+* Localization.AtPrime q := IsLocalization.lift (M := nonZeroDivisors ℤ) hunitZ
  let gQ : ℚ[X] := g.map (Int.castRingHom ℚ)
  haveI : Fact (Irreducible gQ) := ⟨hirr⟩
  let x : Localization.AtPrime q := algebraMap ℤ[X] (Localization.AtPrime q) X
  have hgx : eval₂ i x gQ = 0 := by
    have e1 : eval₂ i x gQ = eval₂ (i.comp (Int.castRingHom ℚ)) x g := Polynomial.eval₂_map _ _ _
    have e2 : i.comp (Int.castRingHom ℚ) = (algebraMap ℤ[X] (Localization.AtPrime q)).comp C := Subsingleton.elim _ _
    have e3 : ∀ r : ℤ[X], algebraMap ℤ[X] (Localization.AtPrime q) r =
        eval₂ ((algebraMap ℤ[X] (Localization.AtPrime q)).comp C) x r := fun r =>
      RingHom.congr_fun (Polynomial.ringHom_ext (f := algebraMap ℤ[X] (Localization.AtPrime q))
        (g := eval₂RingHom ((algebraMap ℤ[X] (Localization.AtPrime q)).comp C) x) (fun a => by simp) (by simp [x])) r
    rw [e1, e2, ← e3, halgS, RingHom.comp_apply, RingHom.comp_apply]
    have : f (algebraMap ℤ[X] A g) = 0 := by
      show Ideal.Quotient.mk _ (algebraMap A (Aaway A c) ((aeval v).toRingHom g)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← aeval_algebraMap_eq]
      exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  let K := AdjoinRoot gQ
  let φK : K →+* Localization.AtPrime q := AdjoinRoot.lift i x hgx
  letI : Algebra K (Localization.AtPrime q) := φK.toAlgebra
  letI algZK : Algebra ℤ[X] K := ((AdjoinRoot.mk gQ).comp (mapRingHom (Int.castRingHom ℚ))).toAlgebra
  have hTK : IsScalarTower ℤ[X] K (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · exact RingHom.congr_fun (Subsingleton.elim ((algebraMap ℤ[X] (Localization.AtPrime q)).comp C)
        (((algebraMap K (Localization.AtPrime q)).comp (algebraMap ℤ[X] K)).comp C)) n
    · show x = φK ((AdjoinRoot.mk gQ) (Polynomial.map (Int.castRingHom ℚ) X))
      rw [Polynomial.map_X, AdjoinRoot.mk_X, AdjoinRoot.lift_root]
  haveI := hTK
  haveI hU2 : Algebra.FormallyUnramified K (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars ℤ[X] K _

  haveI : Module.Finite ℚ K := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hU3 : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI hU4 : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (M := nonZeroDivisors ℤ)
  have hT1 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (Subsingleton.elim _ _)
  haveI := hT1
  haveI hU5 : Algebra.FormallyUnramified ℤ K := Algebra.FormallyUnramified.comp ℤ ℚ K
  have hT2 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := K) (A := Localization.AtPrime q) (Subsingleton.elim _ _)
  haveI := hT2
  haveI hU6 : Algebra.FormallyUnramified ℤ (Localization.AtPrime q) := Algebra.FormallyUnramified.comp ℤ K _

  have hT3 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := Localization.Away c) (A := Localization.AtPrime q)
    (Subsingleton.elim _ _)
  haveI := hT3
  exact Algebra.FormallyUnramified.of_restrictScalars ℤ (Localization.Away c) _

end main
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre"

end LevelPGen
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPGen"

namespace LevelBC
variable {A : Type} [CommRing A] {c d : ℤ} {u : A} {g : ℤ[X]}
set_option synthInstance.maxHeartbeats 800000 in

theorem finite_mul (hfin : Module.Finite (Localization.Away c) (Br A u g c)) :
    Module.Finite (Localization.Away (c * d)) (Br A u g (c * d)) := by
  haveI := hfin
  haveI : Algebra.IsPushout (Localization.Away c) (Localization.Away (c * d)) (Br A u g c) (Br A u g (c * d)) :=
    Algebra.IsPushout.symm inferInstance
  exact Module.Finite.equiv (Algebra.IsPushout.equiv (Localization.Away c) (Localization.Away (c * d))
    (Br A u g c) (Br A u g (c * d))).toLinearEquiv
end LevelBC
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPGen"

open ModularCurve ModularCurve.HpoolLevelRing

theorem essFiniteType_int_congr {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.EssFiniteType ℤ X _ _ i₁) : @Algebra.EssFiniteType ℤ X _ _ i₂ := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : Afin p)
    (hv : (v : ↥(modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∨
      (v : ↥(modularFunctionFieldFull p)) =
        (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹) :
    ∃ (avoid : (ZMod p)[X]) (_ : avoid ≠ 0) (_ : X ∣ avoid) (c₀ : ℤ[X]) (_ : c₀ ≠ 0),
      ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod p))) →
        IsCoprime (g.map (Int.castRingHom (ZMod p))) avoid → ¬ g ∣ c₀ →
        ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ c ≠ 0 ∧ ∀ f : ℤ, f ≠ 0 → c ∣ f →
          Module.Finite (Localization.Away f) (levelRing p f v g) ∧
          Algebra.Etale (Localization.Away f) (levelRing p f v g) ∧
          Module.Free (Localization.Away f) (levelRing p f v g) ∧
          Module.finrank (Localization.Away f) (levelRing p f v g) = (p - 1) * g.natDegree ∧
          ∀ 𝔮 : PrimeSpectrum (Localization.Away f),
            Module.rankAtStalk (R := Localization.Away f) (levelRing p f v g) 𝔮 = (p - 1) * g.natDegree := by
  classical
  have hpP : (p : ℕ).Prime := Fact.out

  obtain ⟨Pu, Pz, hPu, hPz, hne, hmin, hinf, hvu, hvz, e, U, heU, hdeg, hU'⟩ :=
    ModularCurve.HpoolLevelRing.exists_pFibre_dictionary p hp hmem v hv
  haveI := hPu
  haveI := hPz

  obtain ⟨avoid, havoid0, hXavoid, havoidP⟩ := LevelPFibre.exists_avoid (k := ZMod p) U hU'

  obtain ⟨c₀, hc₀0, hunr⟩ :=
    ModularCurve.HpoolLevelRing.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem p hmem v hv
  refine ⟨avoid, havoid0, hXavoid, c₀, hc₀0, fun g hg hD hirr hcop hndvd => ?_⟩

  obtain ⟨hg0bar, hsepU⟩ := havoidP (g.map (Int.castRingHom (ZMod p))) hirr hcop
  have hg0p : ¬ (p : ℤ) ∣ g.coeff 0 := by
    intro hdvd; apply hg0bar
    rw [eval_map, eval₂_at_zero, eq_intCast, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd]
  have hg00 : g.coeff 0 ≠ 0 := fun h => hg0p (by rw [h]; exact dvd_zero _)

  have hpPz : (p : Afin p) ∈ Pz := (hinf.symm ▸ Ideal.mem_span_singleton_self (p : Afin p) : (p : Afin p) ∈ Pu ⊓ Pz).2
  have hcharPz : CharP (Afin p ⧸ Pz) p := by
    haveI : Nontrivial (Afin p ⧸ Pz) := Ideal.Quotient.nontrivial_iff.2 hPz.ne_top
    have hp0 : (p : Afin p ⧸ Pz) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk Pz), Ideal.Quotient.eq_zero_iff_mem]; exact hpPz
    have hdvd : ringChar (Afin p ⧸ Pz) ∣ p := (ringChar.spec _ p).1 hp0
    rcases (Nat.dvd_prime hpP).1 hdvd with h1 | hp'
    · exact absurd h1 CharP.ringChar_ne_one
    · have := ringChar.charP (Afin p ⧸ Pz); rwa [hp'] at this
  have hxz : IsUnit (Ideal.Quotient.mk Pz (aeval v g)) := by

    have h1 : Ideal.Quotient.mk Pz (aeval v g) = Ideal.Quotient.mk Pz (algebraMap ℤ (Afin p) (g.coeff 0)) := by
      rw [← Ideal.Quotient.algebraMap_eq, ← aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 hvz, aeval_def, eval₂_at_zero]
      exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (Afin p ⧸ Pz)) ((Ideal.Quotient.mk Pz).comp (algebraMap ℤ (Afin p)))) _
    rw [h1]
    haveI := hcharPz
    have h2 : Ideal.Quotient.mk Pz (algebraMap ℤ (Afin p) (g.coeff 0)) = ZMod.castHom (dvd_refl p) (Afin p ⧸ Pz) (g.coeff 0 : ZMod p) := by
      rw [map_intCast]
      exact RingHom.congr_fun (Subsingleton.elim ((Ideal.Quotient.mk Pz).comp (algebraMap ℤ (Afin p))) (Int.castRingHom _)) _
    rw [h2]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hg0p
  have heval : e (Ideal.Quotient.mk Pu (aeval v g)) = (g.map (Int.castRingHom (ZMod p))).comp U := by
    have h1 : Ideal.Quotient.mk Pu (aeval v g) = aeval (Ideal.Quotient.mk Pu v) g := by
      rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply]
    have h2 : e (aeval (Ideal.Quotient.mk Pu v) g) = aeval (e (Ideal.Quotient.mk Pu v)) g :=
      (Polynomial.aeval_algHom_apply (e.toRingHom.toIntAlgHom) (Ideal.Quotient.mk Pu v) g).symm
    rw [h1, h2, heU, Polynomial.comp_eq_aeval, show Int.castRingHom (ZMod p) = algebraMap ℤ (ZMod p) from rfl,
      aeval_map_algebraMap]
  have hsep : (e (Ideal.Quotient.mk Pu (aeval v g))).Separable := heval ▸ hsepU
  have hxu : aeval v g ∉ Pu := by
    intro h
    have : e (Ideal.Quotient.mk Pu (aeval v g)) = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
    rw [this] at hsep
    exact Polynomial.not_separable_zero hsep
  have hnzd : ∀ y : Afin p, aeval v g * y ∈ Ideal.span {(p : Afin p)} → y ∈ Ideal.span {(p : Afin p)} :=
    fun y hy => LevelPFibre.mem_span_of_mul_mem hinf hxz hxu hy

  set g0 : ℤ := g.coeff 0 with hg0
  have hpA : (p : Afin p) ≠ 0 := Nat.cast_ne_zero.2 hpP.ne_zero
  have hg0A : algebraMap ℤ (Afin p) g0 ≠ 0 := fun h => hg00 ((algebraMap ℤ (Afin p)).injective_int (by rw [h, map_zero]))
  have hfin0 : Module.Finite (Localization.Away g0) (levelRing p g0 v g) :=
    ModularCurve.HpoolLevelRing.finite_levelRing p hmem v hv g hg hD hg00 g0 hg00 (dvd_refl _)
  have hpt0 : ∀ s : levelRing p g0 v g, (p : levelRing p g0 v g) * s = 0 → s = 0 := by
    intro s hs
    refine LevelPFibre.eq_zero_of_pi_mul_eq_zero v g hpA hnzd hg0A s ?_
    rwa [map_natCast]

  obtain ⟨n', hn'0, hn'p, hkill⟩ := LevelBC.exists_int_kills_torsion (A := Afin p) (u := v) (g := g) hg00 p hpP hfin0 hpt0
  have hc1 : g0 * n' ≠ 0 := mul_ne_zero hg00 hn'0
  have hc1p : ¬ (p : ℤ) ∣ g0 * n' := fun h => (Int.Prime.dvd_mul' hpP h).elim hg0p hn'p
  haveI hflat1 : Module.Flat (Localization.Away (g0 * n')) (levelRing p (g0 * n') v g) := LevelBC.flat_of_kills hc1 hkill
  haveI hfin1 : Module.Finite (Localization.Away (g0 * n')) (levelRing p (g0 * n') v g) := LevelBC.finite_mul hfin0

  have hirrZ : Irreducible g := hg.irreducible_of_irreducible_map (Int.castRingHom (ZMod p)) _ hirr
  have hirrQ : Irreducible (g.map (Int.castRingHom ℚ)) := (hg.irreducible_iff_irreducible_map_fraction_map).1 hirrZ
  have hgen : ∀ (q : Ideal (levelRing p (g0 * n') v g)) [q.IsPrime],
      q.comap (algebraMap (Localization.Away (g0 * n')) _) = ⊥ → Algebra.IsUnramifiedAt (Localization.Away (g0 * n')) q :=
    fun q hqP hq => @LevelPGen.isUnramifiedAt_of_comap_eq_bot (Afin p) _ _ _ v g c₀ (g0 * n') hc1 hg hirrQ hndvd hunr q hqP hq
  haveI : Fact (¬ (p : ℤ) ∣ g0 * n') := ⟨hc1p⟩
  haveI hmax : (LevelPFibre.pIdeal p (g0 * n')).IsMaximal := LevelPFibre.isMaximal_pIdeal p (g0 * n')
  have hF := LevelPFibre.formallyUnramified_int_fibre (A := Afin p) p v g (g0 * n') hinf hxz e hsep
  have hEFT : Algebra.EssFiniteType ℤ (Localization.Away (g0 * n')) :=
    Algebra.EssFiniteType.of_isLocalization _ (Submonoid.powers (g0 * n'))
  have hatp : ∀ (q : Ideal (levelRing p (g0 * n') v g)) [q.IsPrime],
      q.comap (algebraMap (Localization.Away (g0 * n')) _) = LevelBC.pIdeal p (g0 * n') →
      Algebra.IsUnramifiedAt (Localization.Away (g0 * n')) q := by
    intro q hqP hq
    exact @LevelPFibre.isUnramifiedAt_of_fibre (Localization.Away (g0 * n')) (levelRing p (g0 * n') v g) _ _ _ hfin1
      (essFiniteType_int_congr _ _ hEFT)
      p _ (LevelPFibre.pIdeal p (g0 * n')) hmax (LevelPFibre.natCast_mem_pIdeal p _) (LevelPFibre.finite_quotient_pIdeal p _)
      (LevelPFibre.formallyUnramified_int_congr _ _ hF) q hqP ⟨hq.symm⟩

  obtain ⟨N, hN0, hNp, hFE⟩ := LevelBC.exists_etale_int (A := Afin p) (u := v) (g := g) (hfin := hfin1) (hflat := hflat1)
    hc1 p hc1p hmax.isPrime hgen hatp
  refine ⟨g0 * n' * N, fun h => (Int.Prime.dvd_mul' hpP h).elim hc1p hNp, mul_ne_zero hc1 hN0, fun f hf hcf => ?_⟩
  obtain ⟨d', rfl⟩ := hcf

  have hfin2 : Module.Finite (Localization.Away (g0 * n' * N)) (LevelBC.Br (Afin p) v g (g0 * n' * N)) :=
    LevelBC.finite_mul (A := Afin p) (c := g0 * n') (d := N) hfin1
  have hfp2 : Algebra.FinitePresentation (Localization.Away (g0 * n' * N)) (LevelBC.Br (Afin p) v g (g0 * n' * N)) :=
    (Algebra.FinitePresentation.of_finiteType (R := Localization.Away (g0 * n' * N))
      (A := LevelBC.Br (Afin p) v g (g0 * n' * N))).mp (@Module.Finite.finiteType _ _ _ _ _ hfin2)
  have het2 : Algebra.Etale (Localization.Away (g0 * n' * N)) (LevelBC.Br (Afin p) v g (g0 * n' * N)) := ⟨hFE, hfp2⟩
  have hflat2 : Module.Flat (Localization.Away (g0 * n' * N)) (LevelBC.Br (Afin p) v g (g0 * n' * N)) := by
    haveI := het2
    exact Algebra.Smooth.flat (R := Localization.Away (g0 * n' * N)) (A := LevelBC.Br (Afin p) v g (g0 * n' * N))
  have hrk2 : ∀ 𝔮 : PrimeSpectrum (Localization.Away (g0 * n' * N)),
      Module.rankAtStalk (R := Localization.Away (g0 * n' * N)) (LevelBC.Br (Afin p) v g (g0 * n' * N)) 𝔮 = (p - 1) * g.natDegree :=
    @ModularCurve.HpoolLevelRing.rankAtStalk_levelRing_eq p _ _ hmem v hv g hg
      (by rw [← coeff_zero_eq_eval_zero]; exact hg00) (g0 * n' * N) (mul_ne_zero hc1 hN0) hfin2 hflat2

  exact LevelBC.transfer (A := Afin p) (u := v) (g := g) (c := g0 * n' * N) (d := d') hf _ hfin2 het2 hrk2

end
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelBC P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPFibre P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self.LevelPGen"

end S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_self (solution)
