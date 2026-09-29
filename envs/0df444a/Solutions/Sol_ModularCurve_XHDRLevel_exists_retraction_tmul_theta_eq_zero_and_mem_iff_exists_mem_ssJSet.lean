-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_retraction_tmul_theta_eq_zero_and_mem_iff_exists_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c9153f84-9f72-55cf-958a-eb6fd160e62b

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_coe_theta_eq_of_forall_coe_iota0_of_qExpand
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_retraction_tmul_theta_eq_zero_and_mem_iff_exists_mem_ssJSet
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.ProjectiveLine.map_mk ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

namespace HasseH

theorem jqModC_ne_zero' (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have := order_jqModC K
  rw [h, HahnSeries.order_zero] at this
  norm_num at this

theorem jqModC_ne_C (K : Type*) [Field K] (a : K) : jqModC K ≠ HahnSeries.C a := by
  intro h
  have h1 : (jqModC K).coeff (-1) ≠ 0 := by
    have := (mt HahnSeries.coeff_order_eq_zero.mp (jqModC_ne_zero' K))
    rwa [order_jqModC] at this
  rw [h, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num : (-1 : ℤ) ≠ 0)] at h1
  exact h1 rfl

theorem eq_zero_of_mem_ssJSet_of_lt_five' {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] (hq : q < 5) (a : K) (ha : a ∈ ssJSet q K) : a = 0 := by
  have hqp : q.Prime := Fact.out
  have ha2 := pow_q_sq_eq_self_of_mem_ssJSet q ha
  interval_cases q
  · exact absurd hqp (by decide)
  · exact absurd hqp (by decide)
  · exact eq_zero_of_mem_ssJSet_two a ha ha2
  · exact eq_zero_of_mem_ssJSet_three a ha ha2
  · exact absurd hqp (by decide)

theorem jWidth_div_pos {K : Type*} [Field K] [DecidableEq K] (a : K) : 0 < 12 / jWidth a := by
  have h6 : jWidth a ≤ 6 := Nat.le_of_dvd (by norm_num) (jWidth_dvd_six a)
  exact Nat.div_pos (by omega) (jWidth_pos a)

end HasseH

open HasseH in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]

    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∃ v : ↥(chartAlgFin p (ΓM M H) hj),

      σ₀ ((1 : κ) ⊗ₜ[R p] (theta v : ↥(chartAlgFin p (ΓM M H) hj))) = 0 ∧

      (∀ 𝔭 : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)), 𝔭.IsPrime →
        (∃ a ∈ ssJSet p κ,
          (1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∈ 𝔭) →
        ∀ x : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj),
          σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom x) = 0 → σ₀ x ∈ 𝔭) ∧

      (∀ 𝔭 : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)), 𝔭.IsPrime →
        (σ₀ ((1 : κ) ⊗ₜ[R p] v) ∈ 𝔭 ↔
          ∃ a ∈ ssJSet p κ,
            (1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∈ 𝔭)) ∧

      σ₀ ((1 : κ) ⊗ₜ[R p] v) ≠ 0 ∧
      v * (theta v : ↥(chartAlgFin p (ΓM M H) hj)) = algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) (((p : ℕ) : R p) ^ 12) := by
  classical
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩

  obtain ⟨σ, hσ, -⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  obtain ⟨v, w, hv, hw, hvw, hσv⟩ := ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj σ hσ
  have hrig := ModularCurve.XHDRLevel.coe_theta_eq_of_forall_coe_iota0_of_qExpand p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta σ hσ
  have hθv : theta v = w := Subtype.ext ((hrig v).trans hσv)

  obtain ⟨Θ, emb, hinj, hemb, hpin⟩ := ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_and_embedding_comp_retraction_gammaH
    p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta κ σ₀ h0
  haveI hdom : IsDomain (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) := Function.Injective.isDomain emb.toRingHom hinj
  have hemb1 : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), emb (σ₀ ((1 : κ) ⊗ₜ[R p] c)) = Θ c := fun c => by rw [hemb, map_one, one_mul]
  have hembC : ∀ a : κ, emb (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj))) = HahnSeries.C a := fun a => by
    have e : a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) = algebraMap κ (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [e, AlgHom.commutes]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      HahnSeries.ofPowerSeries_C]

  have hj1 : (((iota0 (jChartFin p (ΓN p M H hpM) hj) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = jqModC ℚ := by
    rw [iota0_spec, AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, coe_jAt]
  have hj2 : (((jChartFin p (ΓM M H) hj : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = jqModC ℚ := by
    rw [AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, coe_jAt]
  have hιj : iota0 (jChartFin p (ΓN p M H hpM) hj) = jChartFin p (ΓM M H) hj := Subtype.ext (Subtype.ext (hj1.trans hj2.symm))
  have hΘj : Θ (jChartFin p (ΓM M H) hj) = jqModC κ := by
    rw [hpin (jChartFin p (ΓM M H) hj) (jqModC ℤ) (by rw [coeffMap_jqModC, hj2]), coeffMap_jqModC]
  have hembj : emb ((1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) = jqModC κ := by
    have e1 : Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 ((1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) = (1 : κ) ⊗ₜ[R p] jChartFin p (ΓM M H) hj := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hιj]
    have e2 : (1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj = σ₀ ((1 : κ) ⊗ₜ[R p] jChartFin p (ΓM M H) hj) := by rw [← e1, h0]
    rw [e2, hemb1, hΘj]
  have hinj' : ∀ s t : κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj), emb s = emb t → s = t := fun s t h => hinj h

  have hΘv_small : p < 5 → Θ v = jqModC κ ^ (p - 1) := fun hp5 => by
    obtain ⟨x, hxℚ, hxκ⟩ := exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five p hp5
    rw [hpin v x (hxℚ.trans hv.symm), hxκ κ]
  have hΘv_large : 5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      Θ v = ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := fun hp5 S hS => by
    obtain ⟨x, hxℚ, hxκ⟩ := exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet p hp5
    rw [hpin v x (hxℚ.trans hv.symm), hxκ κ S hS]
  have hΘv0 : Θ v ≠ 0 := by
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · rw [hΘv_small hp5]; exact pow_ne_zero _ (jqModC_ne_zero' κ)
    · rw [hΘv_large hp5 (ssJSet_finite p κ).toFinset (fun a => Set.Finite.mem_toFinset _)]
      exact Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (sub_ne_zero.mpr (jqModC_ne_C κ a))

  have hd : σ₀ ((1 : κ) ⊗ₜ[R p] v) ≠ 0 := fun h => hΘv0 (by rw [← hemb1, h, map_zero])

  have ha : σ₀ ((1 : κ) ⊗ₜ[R p] (theta v : ↥(chartAlgFin p (ΓM M H) hj))) = 0 := by
    have hprod : σ₀ ((1 : κ) ⊗ₜ[R p] v) * σ₀ ((1 : κ) ⊗ₜ[R p] (theta v : ↥(chartAlgFin p (ΓM M H) hj))) = 0 := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hθv, hvw]
      have hz : (1 : κ) ⊗ₜ[R p] (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) (((p : ℕ) : R p) ^ 12)) = 0 := by
        rw [← Algebra.TensorProduct.includeRight_apply (R := R p) (A := κ), AlgHom.commutes,
          Algebra.TensorProduct.algebraMap_apply, map_pow, map_natCast, CharP.cast_eq_zero κ p,
          zero_pow (by norm_num), TensorProduct.zero_tmul]
      rw [hz, map_zero]
    exact (mul_eq_zero.mp hprod).resolve_left hd

  have hc_large : 5 ≤ p → ∀ S : Finset κ, (∀ a, a ∈ S ↔ a ∈ ssJSet p κ) →
      σ₀ ((1 : κ) ⊗ₜ[R p] v) = ∏ a ∈ S, ((1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj))) ^ (12 / jWidth a) := by
    intro hp5 S hS
    apply hinj'
    rw [hemb1, hΘv_large hp5 S hS, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_pow, map_sub, hembj, hembC]
  have hc_small : p < 5 → σ₀ ((1 : κ) ⊗ₜ[R p] v) = ((1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj) ^ (p - 1) := fun hp5 => by
    apply hinj'
    rw [hemb1, hΘv_small hp5, map_pow, hembj]
  have hc : ∀ 𝔭 : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)), 𝔭.IsPrime →
      (σ₀ ((1 : κ) ⊗ₜ[R p] v) ∈ 𝔭 ↔ ∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∈ 𝔭) := by
    intro 𝔭 h𝔭
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp1 : 0 < p - 1 := by have := hpp.two_le; omega
      rw [hc_small hp5]
      constructor
      · intro h
        refine ⟨0, zero_mem_ssJSet_of_lt_five hp5, ?_⟩
        rw [TensorProduct.zero_tmul, sub_zero]
        exact h𝔭.mem_of_pow_mem _ h
      · rintro ⟨a, ha', hmem⟩
        have ha0 : a = 0 := eq_zero_of_mem_ssJSet_of_lt_five' p hp5 a ha'
        rw [ha0, TensorProduct.zero_tmul, sub_zero] at hmem
        exact Ideal.pow_mem_of_mem 𝔭 hmem _ hp1
    · have hS : ∀ a, a ∈ (ssJSet_finite p κ).toFinset ↔ a ∈ ssJSet p κ := fun a => Set.Finite.mem_toFinset _
      rw [hc_large hp5 _ hS]
      haveI := h𝔭
      constructor
      · intro h
        obtain ⟨a, haS, ha'⟩ := Ideal.IsPrime.prod_mem_iff.mp h
        exact ⟨a, (hS a).mp haS, h𝔭.mem_of_pow_mem _ ha'⟩
      · rintro ⟨a, ha', hmem⟩
        rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem ((hS a).mpr ha')]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem 𝔭 hmem _ (jWidth_div_pos a))

  have hb := ModularCurve.XHDRLevel.retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH p M H hpM hpM2 hHp hj iota0 iota0_spec
    theta htheta κ σ₀ h0
  refine ⟨v, ha, hb, hc, hd, ?_⟩
  rw [hθv]; exact hvw

end S_ModularCurve_XHDRLevel_exists_retraction_tmul_theta_eq_zero_and_mem_iff_exists_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_retraction_tmul_theta_eq_zero_and_mem_iff_exists_mem_ssJSet (solution)
