-- Prove2me | solution 1 for ModularCurve.XHDRLevel.retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9e84691c-e848-5733-810e-28cff0c1fb1a

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_finite_minimalPrimes_tensor_chartAlgFin_gammaH_and_ncard_eq_two
import Theorems.Thm_ModularCurve_XHDRLevel_isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.ProjectiveLine.map_mk ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

noncomputable section

namespace CrossBRed

variable (p : ℕ) [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)

theorem residue_surjective : Function.Surjective (GaloisRep.ratLocalizedAtResidue p) := by
  intro x
  refine ⟨((x.val : ℕ) : ℤp), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

scoped instance isLocalRing_Zp : IsLocalRing ℤp :=
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  inferInstance

theorem maximalIdeal_eq_span : IsLocalRing.maximalIdeal ℤp = Ideal.span {((p : ℕ) : ℤp)} := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := by
    show IsLocalization _ _; infer_instance
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)}) ℤp, Ideal.map_span, Set.image_singleton,
    map_natCast]

theorem ker_residue_eq_span : RingHom.ker (GaloisRep.ratLocalizedAtResidue p) = Ideal.span {((p : ℕ) : ℤp)} := by
  rw [IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (residue_surjective p)), maximalIdeal_eq_span]

def quotEquiv : (ℤp ⧸ Ideal.span {((p : ℕ) : ℤp)}) ≃ₐ[ℤp] ZMod p :=
  (Ideal.quotientEquivAlgOfEq ℤp (ker_residue_eq_span p).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId ℤp (ZMod p)) (residue_surjective p))

private theorem _root_.CrossBRed.ringHom_ext {S : Type*} [Semiring S] (f g : ℤp →+* S) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

p2m_export "CrossBRed" "ringHom_ext"

theorem isReduced_tensor (𝒪 : Type) [CommRing 𝒪] [Algebra ℤp 𝒪]
    (hred : IsReduced (𝒪 ⧸ Ideal.span {((p : ℕ) : 𝒪)}))
    (κ : Type) [Field κ] [CharP κ p] [Algebra ℤp κ] : IsReduced (κ ⊗[ℤp] 𝒪) := by
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  haveI : IsScalarTower ℤp (ZMod p) κ :=
    IsScalarTower.of_algebraMap_eq' (ringHom_ext p _ _)

  have hmap : (Ideal.span {((p : ℕ) : ℤp)}).map (algebraMap ℤp 𝒪) = Ideal.span {((p : ℕ) : 𝒪)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let e₁ : (𝒪 ⧸ Ideal.span {((p : ℕ) : 𝒪)}) ≃+* (ZMod p) ⊗[ℤp] 𝒪 :=
    (Ideal.quotEquivOfEq hmap.symm).trans
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor 𝒪 (Ideal.span {((p : ℕ) : ℤp)})).toRingEquiv.trans
        (Algebra.TensorProduct.congr (quotEquiv p) (AlgEquiv.refl (R := ℤp) (A₁ := 𝒪))).toRingEquiv)
  haveI : IsReduced ((ZMod p) ⊗[ℤp] 𝒪) := isReduced_of_injective e₁.symm.toRingHom e₁.symm.injective

  haveI : IsReduced (κ ⊗[ZMod p] ((ZMod p) ⊗[ℤp] 𝒪)) :=
    Algebra.isReduced_tensorProduct_of_perfectField (ZMod p) ((ZMod p) ⊗[ℤp] 𝒪) κ
  let e₂ : κ ⊗[ZMod p] ((ZMod p) ⊗[ℤp] 𝒪) ≃ₐ[κ] κ ⊗[ℤp] 𝒪 :=
    Algebra.TensorProduct.cancelBaseChange ℤp (ZMod p) κ κ 𝒪
  exact isReduced_of_injective e₂.symm.toRingHom e₂.symm.injective

end CrossBRed
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed"

namespace CrossB

section Zp
variable (p : ℕ) [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)

theorem residue_surjective : Function.Surjective (GaloisRep.ratLocalizedAtResidue p) := by
  intro x
  refine ⟨((x.val : ℕ) : ℤp), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

scoped instance isLocalRing_Zp : IsLocalRing ℤp :=
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  inferInstance

theorem ker_residue_eq_maximalIdeal :
    RingHom.ker (GaloisRep.ratLocalizedAtResidue p) = IsLocalRing.maximalIdeal ℤp :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (residue_surjective p))

theorem maximalIdeal_eq_span : IsLocalRing.maximalIdeal ℤp = Ideal.span {((p : ℕ) : ℤp)} := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := by
    show IsLocalization _ _; infer_instance
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)}) ℤp, Ideal.map_span, Set.image_singleton,
    map_natCast]

theorem span_p_isMaximal : (Ideal.span {((p : ℕ) : ℤp)}).IsMaximal := by
  rw [← maximalIdeal_eq_span]; exact IsLocalRing.maximalIdeal.isMaximal ℤp

theorem ker_residue_eq_span : RingHom.ker (GaloisRep.ratLocalizedAtResidue p) = Ideal.span {((p : ℕ) : ℤp)} := by
  rw [ker_residue_eq_maximalIdeal, maximalIdeal_eq_span]

def quotEquiv : (ℤp ⧸ Ideal.span {((p : ℕ) : ℤp)}) ≃ₐ[ℤp] ZMod p :=
  (Ideal.quotientEquivAlgOfEq ℤp (ker_residue_eq_span p).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId ℤp (ZMod p)) (residue_surjective p))

private theorem _root_.CrossB.ringHom_ext {S : Type*} [Semiring S] (f g : ℤp →+* S) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

p2m_export "CrossB" "ringHom_ext"
end Zp
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed"

section Generic
variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)

theorem map_id_bijective {A : Type} [CommRing A] [Algebra ℤp A] (w : A ≃ₐ[ℤp] A) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom) := by
  have h1 : ∀ z, Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id κ κ) w.symm.toAlgHom z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x c =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have h2 : ∀ z, Algebra.TensorProduct.map (AlgHom.id κ κ) w.symm.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x c =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

theorem comap_mem_minimalPrimes_of_bijective {T : Type*} [CommRing T] (f : T →+* T)
    (hf : Function.Bijective f) {P : Ideal T} (hP : P ∈ minimalPrimes T) : P.comap f ∈ minimalPrimes T := by
  have h := Ideal.minimalPrimes_comap_of_surjective hf.2 hP
  rwa [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot f).mp hf.1] at h

theorem one_tmul_natCast_mul [CharP κ p] {A : Type*} [CommRing A] [Algebra ℤp A] (c : A) :
    (1 : κ) ⊗ₜ[ℤp] (((p : ℕ) : A) * c) = 0 := by
  rw [show ((p : ℕ) : A) * c = ((p : ℕ) : ℤp) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

theorem isIntegral_of_mem {K : IntermediateField ℚ (LaurentSeries ℚ)} (j : ↥K) [Fact (j ≠ 0)]
    (S : Subalgebra κ (κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j)))
    (hS : (1 : κ) ⊗ₜ[ℤp] TwoChartIntegralModel.jChartFin ℤp ↥K j ∈ S)
    (z : κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j)) : IsIntegral S z := by
  induction z using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | add x y hx hy => exact hx.add hy
  | tmul x b =>
    have hxb : x ⊗ₜ[ℤp] b = algebraMap κ (κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j)) x *
        ((1 : κ) ⊗ₜ[ℤp] b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hxb]
    refine IsIntegral.mul ?_ ?_
    · exact isIntegral_algebraMap (R := S) (x := ⟨_, S.algebraMap_mem x⟩)
    ·
      obtain ⟨P, hPm, hP⟩ := (TwoChartIntegralModel.mem_chartAlg_iff ℤp ↥K).mp b.2

      let incl : ↥(Algebra.adjoin ℤp {j}) →ₐ[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j) :=
        Subalgebra.inclusion (TwoChartIntegralModel.adjoin_le_chartAlg ℤp ↥K {j})
      let ρₐ : ↥(Algebra.adjoin ℤp {j}) →ₐ[ℤp] κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j) :=
        (Algebra.TensorProduct.includeRight : ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j) →ₐ[ℤp] κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j)).comp incl

      have hρS : ∀ a : ↥(Algebra.adjoin ℤp {j}), ρₐ a ∈ S := by
        rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          have : ρₐ ⟨y, Algebra.subset_adjoin (by rw [hy]; rfl)⟩ =
              (1 : κ) ⊗ₜ[ℤp] TwoChartIntegralModel.jChartFin ℤp ↥K j := by
            subst hy; rfl
          rw [this]
          exact hS
        | algebraMap r =>
          have : (⟨algebraMap ℤp ↥K r, Subalgebra.algebraMap_mem _ r⟩ :
              ↥(Algebra.adjoin ℤp {j})) = algebraMap ℤp _ r := rfl
          rw [this, AlgHom.commutes, IsScalarTower.algebraMap_apply ℤp κ (κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j))]
          exact S.algebraMap_mem _
        | add y y' hy hy' h h' =>
          have : (⟨y + y', add_mem hy hy'⟩ : ↥(Algebra.adjoin ℤp {j})) = ⟨y, hy⟩ + ⟨y', hy'⟩ := rfl
          rw [this, map_add]
          exact S.add_mem h h'
        | mul y y' hy hy' h h' =>
          have : (⟨y * y', mul_mem hy hy'⟩ : ↥(Algebra.adjoin ℤp {j})) = ⟨y, hy⟩ * ⟨y', hy'⟩ := rfl
          rw [this, map_mul]
          exact S.mul_mem h h'

      have hroot : (P.map ρₐ.toRingHom).eval ((1 : κ) ⊗ₜ[ℤp] b) = 0 := by
        have h1 : P.eval₂ incl.toRingHom b = 0 := by
          apply Subtype.val_injective
          have := Polynomial.hom_eval₂ P incl.toRingHom (TwoChartIntegralModel.chartAlgFin ℤp ↥K j).val.toRingHom b
          have hcomp : (TwoChartIntegralModel.chartAlgFin ℤp ↥K j).val.toRingHom.comp incl.toRingHom =
              algebraMap ↥(Algebra.adjoin ℤp {j}) ↥K :=
            RingHom.ext fun _ => rfl
          rw [hcomp] at this
          exact this.trans hP
        have h2 := Polynomial.hom_eval₂ P incl.toRingHom
          (Algebra.TensorProduct.includeRight : ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j) →ₐ[ℤp] κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j)).toRingHom b
        rw [h1, map_zero] at h2
        rw [Polynomial.eval_map]
        exact h2.symm

      have hlifts : P.map ρₐ.toRingHom ∈ Polynomial.lifts (algebraMap S (κ ⊗[ℤp] ↥(TwoChartIntegralModel.chartAlgFin ℤp ↥K j))) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map, Subalgebra.setRange_algebraMap]
        exact hρS _
      obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hPm.map _)
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQmap]
      exact hroot

end Generic
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed"

end CrossB
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossB"

namespace CrossB

section Frame
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (κ : Type) [Field κ] [Algebra (R p) κ]

set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)

theorem iota0_jChartFin
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) :
    iota0 (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj := by
  apply Subtype.ext; apply Subtype.ext
  rw [iota0_spec]
  show ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)
  rw [coe_jAt, coe_jAt]

theorem ker_retraction_mem_minimalPrimes [IsDomain (κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))]
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hιj : iota0 (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj)
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) := by
  let φ : κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) := Algebra.TensorProduct.map (AlgHom.id κ κ) iota0
  haveI hP : (RingHom.ker σ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hK : (1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓM M H) hj ∈ φ.range :=
    φ.mem_range.2 ⟨(1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj, by
      show Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 _ = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hιj]⟩
  haveI : Algebra.IsIntegral ↥φ.range (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) :=
    ⟨fun z => isIntegral_of_mem p κ (jAt (ΓM M H) hj) φ.range hK z⟩
  have hcomap : (RingHom.ker σ₀.toRingHom).comap (algebraMap ↥φ.range (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨t, ht⟩ hmem
    obtain ⟨s, rfl⟩ := φ.mem_range.1 ht
    rw [Ideal.mem_comap, RingHom.mem_ker] at hmem
    change σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 s) = 0 at hmem
    rw [h0] at hmem
    subst hmem
    rw [Ideal.mem_bot]
    exact Subtype.ext (map_zero φ)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))) ≤ RingHom.ker σ₀.toRingHom)
  suffices hQP : Q = RingHom.ker σ₀.toRingHom by rw [← hQP]; exact hQ
  by_contra hne
  haveI : Q.IsPrime := hQ.1.1
  obtain ⟨-, x, hxP, hxQ⟩ := SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hQle hne)
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥φ.range) hQle ⟨hxP, hxQ⟩
    (Algebra.IsIntegral.isIntegral x)
  rw [hcomap] at hlt
  exact not_lt_bot hlt

theorem jqModC_ne_C (K : Type*) [Field K] (a : K) : jqModC K ≠ HahnSeries.C a := by
  intro h
  have h1 := congrArg HahnSeries.order h
  rw [order_jqModC] at h1
  by_cases ha : a = 0
  · rw [ha, map_zero, HahnSeries.order_zero] at h1; exact absurd h1 (by norm_num)
  · rw [HahnSeries.order_C] at h1; exact absurd h1 (by norm_num)

theorem eq_zero_of_mem_ssJSet_of_lt_five' {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] (hq : q < 5) (a : K) (ha : a ∈ ssJSet q K) : a = 0 := by
  have hprime : q.Prime := Fact.out
  have ha2 := pow_q_sq_eq_self_of_mem_ssJSet q ha
  have hq23 : q = 2 ∨ q = 3 := by
    interval_cases q <;> first | exact absurd hprime (by decide) | simp
  rcases hq23 with rfl | rfl
  · exact eq_zero_of_mem_ssJSet_two a ha ha2
  · exact eq_zero_of_mem_ssJSet_three a ha ha2

theorem jWidth_div_pos {K : Type*} [Field K] [DecidableEq K] (a : K) : 0 < 12 / jWidth a := by
  have h6 : jWidth a ≤ 6 := Nat.le_of_dvd (by norm_num) (jWidth_dvd_six a)
  exact Nat.div_pos (by omega) (jWidth_pos a)

theorem tmul_ogg_mem_and_ne_zero [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hιj : iota0 (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj)
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (Θ : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries κ) (emb : κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[κ] LaurentSeries κ)
    (hemb : Function.Injective emb)
    (hembσ : ∀ (a : κ) (c : ↥(chartAlgFin p (ΓM M H) hj)), emb (σ₀ (a ⊗ₜ[ℤp] c)) = HahnSeries.C a * Θ c)
    (hΘpin : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries ℤ), coeffMap (Int.castRingHom ℚ) y = (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        Θ c = coeffMap (Int.castRingHom κ) y)
    (v : ↥(chartAlgFin p (ΓM M H) hj)) (hvq : (((v : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p)
    (𝔭 : Ideal (κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))) [𝔭.IsPrime]
    (hss : ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∈ 𝔭) :
    σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ∈ 𝔭 ∧ σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ≠ 0 := by
  have hpp : p.Prime := Fact.out
  have hΘj : Θ (jChartFin p (ΓM M H) hj) = jqModC κ := by
    rw [hΘpin (jChartFin p (ΓM M H) hj) (jqModC ℤ)]
    · exact coeffMap_jqModC _
    · rw [coeffMap_jqModC]
      show jqModC ℚ = ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)
      rw [coe_jAt]
  have hσ₀j : σ₀ ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓM M H) hj) = (1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj := by
    rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hemb1 : ∀ c, emb (σ₀ ((1 : κ) ⊗ₜ[ℤp] c)) = Θ c := fun c => by rw [hembσ, map_one, one_mul]
  have hembj : emb ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj) = jqModC κ := by rw [← hσ₀j, hemb1, hΘj]
  have hemba : ∀ a : κ, emb (a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj))) = HahnSeries.C a := fun a => by
    have : a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) = algebraMap κ _ a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, AlgHom.commutes, HahnSeries.C_apply]
    show HahnSeries.ofPowerSeries ℤ κ (PowerSeries.C a) = _
    exact HahnSeries.ofPowerSeries_C a
  have hΘv5 : 5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      Θ v = ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := fun hp5 S hS => by
    obtain ⟨y, hyℚ, hyκ⟩ := exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet p hp5
    rw [hΘpin v y (hyℚ.trans hvq.symm)]
    exact hyκ κ S hS
  have hΘv_small : p < 5 → Θ v = jqModC κ ^ (p - 1) := fun hp5 => by
    obtain ⟨y, hyℚ, hyκ⟩ := exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five p hp5
    rw [hΘpin v y (hyℚ.trans hvq.symm)]
    exact hyκ κ
  have hv5 : 5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      σ₀ ((1 : κ) ⊗ₜ[ℤp] v) = ∏ a ∈ S, ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj -
        a ⊗ₜ[ℤp] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj))) ^ (12 / jWidth a) := fun hp5 S hS => by
    apply hemb
    rw [hemb1, hΘv5 hp5 S hS, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_pow, map_sub, hembj, hemba]
  have hv_small : p < 5 → σ₀ ((1 : κ) ⊗ₜ[ℤp] v) = ((1 : κ) ⊗ₜ[ℤp] jChartFin p (ΓN p M H hpM) hj) ^ (p - 1) := fun hp5 => by
    apply hemb
    rw [hemb1, hΘv_small hp5, map_pow, hembj]
  constructor
  · obtain ⟨a, ha, hmem⟩ := hss
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp1 : 0 < p - 1 := by have := hpp.one_lt; omega
      have ha0 : a = 0 := eq_zero_of_mem_ssJSet_of_lt_five' p hp5 a ha
      rw [ha0, TensorProduct.zero_tmul, sub_zero] at hmem
      rw [hv_small hp5]
      exact Ideal.pow_mem_of_mem 𝔭 hmem _ hp1
    · have hS : ∀ a, a ∈ (ssJSet_finite p κ).toFinset ↔ a ∈ ssJSet p κ := fun a => Set.Finite.mem_toFinset _
      rw [hv5 hp5 _ hS, Finset.prod_eq_mul_prod_diff_singleton_of_mem ((hS a).mpr ha)]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem 𝔭 hmem _ (jWidth_div_pos a))
  · intro h
    have h' := congrArg emb h
    rw [hemb1, map_zero] at h'
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · rw [hΘv_small hp5] at h'
      exact pow_ne_zero _ (fun e => jqModC_ne_C κ 0 (by rw [e, map_zero])) h'
    · have hS : ∀ a, a ∈ (ssJSet_finite p κ).toFinset ↔ a ∈ ssJSet p κ := fun a => Set.Finite.mem_toFinset _
      rw [hΘv5 hp5 _ hS, Finset.prod_eq_zero_iff] at h'
      obtain ⟨a, -, ha⟩ := h'
      exact jqModC_ne_C κ a (sub_eq_zero.mp ((pow_eq_zero_iff (jWidth_div_pos a).ne').mp ha))

set_option maxHeartbeats 25600000 in
theorem ker_comp_le_comap [CharP κ p] [IsReduced (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))] [IsDomain (κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))]
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hιj : iota0 (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hfin : (minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))).Finite) (hcard : (minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj))).ncard = 2)
    (v : ↥(chartAlgFin p (ΓM M H) hj)) (hvv' : v * theta v = algebraMap ℤp ↥(chartAlgFin p (ΓM M H) hj) ((p : ℕ) : ℤp) ^ 12)
    (hθv0 : σ₀ ((1 : κ) ⊗ₜ[ℤp] theta v) = 0)
    (𝔭 : Ideal (κ ⊗[ℤp] ↥(chartAlgFin p (ΓN p M H hpM) hj))) [𝔭.IsPrime]
    (hv𝔭 : σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ∈ 𝔭) (hv0 : σ₀ ((1 : κ) ⊗ₜ[ℤp] v) ≠ 0) :
    RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom ≤ 𝔭.comap σ₀.toRingHom := by
  have hpp : p.Prime := Fact.out
  have hQ₀ : RingHom.ker σ₀.toRingHom ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) :=
    ker_retraction_mem_minimalPrimes p M H hpM hj κ iota0 hιj σ₀ h0
  have hQ₁eq : RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom =
      (RingHom.ker σ₀.toRingHom).comap (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← RingHom.comap_ker]; rfl
  have hQ₁ : RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom ∈ minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) := by
    rw [hQ₁eq]; exact comap_mem_minimalPrimes_of_bijective _ (map_id_bijective p κ theta) hQ₀
  have hvQ₁ : (1 : κ) ⊗ₜ[ℤp] v ∈ RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom := by
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply, hθv0]
  have hvQ₀ : (1 : κ) ⊗ₜ[ℤp] v ∉ RingHom.ker σ₀.toRingHom := fun h => hv0 (RingHom.mem_ker.mp h)
  have hne : RingHom.ker σ₀.toRingHom ≠ RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom :=
    fun h => hvQ₀ (h ▸ hvQ₁)
  have hall : minimalPrimes (κ ⊗[ℤp] ↥(chartAlgFin p (ΓM M H) hj)) = {RingHom.ker σ₀.toRingHom, RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom} :=
    (Set.eq_of_subset_of_ncard_le
      (Set.insert_subset_iff.mpr ⟨hQ₀, Set.singleton_subset_iff.mpr hQ₁⟩)
      (by rw [hcard, Set.ncard_pair hne]) hfin).symm
  have hle : RingHom.ker σ₀.toRingHom ≤ 𝔭.comap σ₀.toRingHom := by
    rw [RingHom.ker_eq_comap_bot]; exact Ideal.comap_mono bot_le
  have hvq : (1 : κ) ⊗ₜ[ℤp] v ∈ 𝔭.comap σ₀.toRingHom := by rw [Ideal.mem_comap]; exact hv𝔭
  have hp𝒪 : algebraMap ℤp ↥(chartAlgFin p (ΓM M H) hj) ((p : ℕ) : ℤp) ∈ nonZeroDivisors ↥(chartAlgFin p (ΓM M H) hj) := by
    refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
    have h' := congrArg (algebraMap ↥(chartAlgFin p (ΓM M H) hj) ↥(qExpFunctionFieldC ℚ (ΓM M H))) h
    rw [← IsScalarTower.algebraMap_apply, map_zero, map_natCast] at h'
    exact (Nat.cast_ne_zero.mpr hpp.ne_zero) h'
  obtain ⟨Q, hQ, hQne, hQle⟩ :=
    Algebra.TensorProduct.exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem ℤp ((p : ℕ) : ℤp)
      (span_p_isMaximal p) ↥(chartAlgFin p (ΓM M H) hj) hp𝒪 κ (by rw [map_natCast]; exact CharP.cast_eq_zero κ p) v (theta v) 12 hvv'
      (RingHom.ker σ₀.toRingHom) (𝔭.comap σ₀.toRingHom) hQ₀ hle hvQ₀ hvq
  rw [hall] at hQ
  rcases hQ with h | h
  · exact absurd h hQne
  · rw [Set.mem_singleton_iff] at h
    rw [← h]; exact hQle

end Frame
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossB"

end CrossB
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossB"

set_option maxHeartbeats 12800000 in
open CrossB in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∀ 𝔭 : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)), 𝔭.IsPrime →
      (∃ a ∈ ssJSet p κ,
        (1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∈ 𝔭) →
      ∀ x : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj),
        σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom x) = 0 → σ₀ x ∈ 𝔭 := by
  intro 𝔭 h𝔭 hss x hx
  classical
  haveI := h𝔭

  obtain ⟨σ, hσq, -⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  obtain ⟨v, w, hvq, -, hvw, hσv⟩ := ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj σ hσq
  have hθ := ModularCurve.XHDRLevel.coe_theta_eq_of_forall_coe_iota0_of_qExpand p M H hpM hpM2 hHp hj
    iota0 iota0_spec theta htheta σ hσq
  have hθv : theta v = w := Subtype.ext ((hθ v).trans hσv)
  obtain ⟨Θ, emb, hemb, hembσ, hΘpin⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH p M H hpM hpM2 hHp hj
      iota0 iota0_spec theta htheta κ σ₀ h0
  haveI : IsDomain (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := Function.Injective.isDomain emb.toRingHom hemb
  have hιj := iota0_jChartFin p M H hpM hj iota0 iota0_spec

  obtain ⟨hv𝔭, hv0⟩ := tmul_ogg_mem_and_ne_zero p M H hpM hj κ iota0 hιj σ₀ h0 Θ emb hemb hembσ hΘpin v hvq 𝔭 hss

  have hθv0 : σ₀ ((1 : κ) ⊗ₜ[R p] theta v) = 0 := by
    have hprod : σ₀ ((1 : κ) ⊗ₜ[R p] v) * σ₀ ((1 : κ) ⊗ₜ[R p] theta v) = 0 := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hθv, hvw, map_pow, map_natCast, pow_succ',
        one_tmul_natCast_mul p κ, map_zero]
    exact (mul_eq_zero.mp hprod).resolve_left hv0
  have hvv' : v * theta v = algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) ((p : ℕ) : R p) ^ 12 := by rw [hθv, hvw, map_pow]
  obtain ⟨hfin, hcard⟩ := ModularCurve.XHDRLevel.finite_minimalPrimes_tensor_chartAlgFin_gammaH_and_ncard_eq_two
    p M H hpM hpM2 hHp hj κ

  haveI hred : IsReduced (κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := by
    obtain ⟨hredM, -⟩ :=
      ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH p M H hpM hpM2 hHp hj
    exact CrossBRed.isReduced_tensor p ↥(chartAlgFin p (ΓM M H) hj) hredM κ
  exact Ideal.mem_comap.mp (ker_comp_le_comap p M H hpM hj κ iota0 hιj theta σ₀ h0 hfin hcard v hvv' hθv0 𝔭 hv𝔭 hv0
    (by rw [RingHom.mem_ker]; exact hx))

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossBRed P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.CrossB"

end S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH (solution)
