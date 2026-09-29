-- Prove2me | solution 1 for ModularCurve.DRModel.map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/059de0af-d517-5354-a3a5-38466009bb94

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode"
p2m_attr_erase "simp" "ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve AlgebraicCurve Polynomial

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
    (W₀ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull p), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)))
    (h𝔭 : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)), a ∈ 𝔭 ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits))
    (e : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)) ⧸ 𝔭) ≃+* (ZMod p)[X])
    (hej : e (Ideal.Quotient.mk 𝔭
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X)
    (u : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hu : ((u : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = modularUnitSeries p)
    (κ : Type u) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (S : Finset κ) (hS : ∀ a, a ∈ S ↔ a ∈ ssJSet p κ) :
    (e (Ideal.Quotient.mk 𝔭 u)).map (ZMod.castHom (dvd_refl p) κ) =
      ∏ a ∈ S, (X - C a) ^ (12 / jWidth a) := by
  classical

  set j : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
    TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) with hjdef

  obtain ⟨x, hx, hxκ⟩ :=
    ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet p hp

  obtain ⟨P, hP⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    (ZMod.ringHom_surjective _) (e (Ideal.Quotient.mk 𝔭 u))

  set φ : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* (ZMod p)[X] :=
    e.toRingHom.comp (Ideal.Quotient.mk 𝔭) with hφdef
  have hφj : φ j = X := hej
  have hφP : φ (aeval j P) = P.map (Int.castRingHom (ZMod p)) := by
    have h1 : (φ.comp (aeval j).toRingHom) = mapRingHom (Int.castRingHom (ZMod p)) := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_int ((φ.comp (aeval j).toRingHom).comp C)
          ((mapRingHom (Int.castRingHom (ZMod p))).comp C)
        exact congrArg (fun g : ℤ →+* (ZMod p)[X] => g a) this
      · simp [hφj]
    exact congrArg (fun g : ℤ[X] →+* (ZMod p)[X] => g P) h1
  have hdiff : u - aeval j P ∈ 𝔭 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply e.injective
    rw [map_zero, map_sub, map_sub]
    change e (Ideal.Quotient.mk 𝔭 u) - φ (aeval j P) = 0
    rw [hφP, hP, sub_self]

  set z : LaurentSeries ℤ := x - aeval (jqModC ℤ) P with hzdef

  set ψ : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* LaurentSeries ℚ :=
    (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).comp (algebraMap ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ↥(modularFunctionFieldFull p)) with hψdef
  have hψ : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ψ b = ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) := fun b => rfl
  have hψaeval : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ψ (aeval b P) = aeval (ψ b) P := fun b => by
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have hjq : ψ j = coeffMap (Int.castRingHom ℚ) (jqModC ℤ) := by
    rw [hψ]
    change ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = (jqModC ℤ).map (Int.castRingHom ℚ)
    rw [IgusaScheme.coe_jFull, ← jqModC_rat, jqModC_eq_map_intCast]
  have hzq : ψ (u - aeval j P) = coeffMap (Int.castRingHom ℚ) z := by
    rw [map_sub, hψaeval, hjq, hψ, hu, ← hx, hzdef, map_sub, aeval_def, aeval_def,
      Polynomial.hom_eval₂]
    congr 2
    exact RingHom.ext_int _ _

  have hz0 : coeffMap (Int.castRingHom (ZMod p)) z = 0 := by
    by_contra hne
    have hmem : ((u - aeval j P : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits := (h𝔭 _).mp hdiff
    set f : ↥(modularFunctionFieldFull p) := ((u - aeval j P : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) with hfdef
    have hfz : (f : LaurentSeries ℚ) = coeffMap (Int.castRingHom ℚ) z := hzq
    have hcz : coeffMap (Int.castRingHom ℚ) z ≠ 0 := by
      intro h
      apply hne
      have hz : z = 0 := by
        ext k
        have hk := congrArg (fun w : LaurentSeries ℚ => w.coeff k) h
        simpa [coeffMap_coeff] using hk
      rw [hz, map_zero]
    have hf0 : f ≠ 0 := by
      intro h
      apply hcz
      rw [← hfz, h]
      rfl
    have hcoeinv : ((f⁻¹ : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ)
        = ((f : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ)⁻¹ :=
      map_inv₀ (algebraMap (↥(modularFunctionFieldFull p)) (LaurentSeries ℚ)) f
    have hinv : f⁻¹ ∈ W₀ := (hW₀ _).mpr ⟨1, z, hne, by
      rw [map_one, hcoeinv, hfz, inv_mul_cancel₀ hcz]⟩
    rw [ValuationSubring.mem_nonunits_iff] at hmem
    have h1 : W₀.valuation f⁻¹ ≤ 1 := (W₀.valuation_le_one_iff _).mpr hinv
    have hlt : W₀.valuation (f⁻¹ * f) < 1 :=
      calc W₀.valuation (f⁻¹ * f) = W₀.valuation f⁻¹ * W₀.valuation f := map_mul _ _ _
        _ ≤ 1 * W₀.valuation f := mul_le_mul_left h1 _
        _ = W₀.valuation f := one_mul _
        _ < 1 := hmem
    rw [inv_mul_cancel₀ hf0, map_one] at hlt
    exact lt_irrefl _ hlt

  have hxκ' := hxκ κ S hS
  have hzκ : coeffMap (Int.castRingHom κ) z = 0 := by
    have h1 : coeffMap (Int.castRingHom κ) z =
        coeffMap (ZMod.castHom (dvd_refl p) κ) (coeffMap (Int.castRingHom (ZMod p)) z) := by
      rw [coeffMap_coeffMap]; exact coeffMap_congr (RingHom.ext_int _ _) z
    rw [h1, hz0, map_zero]
  have haevalκ : coeffMap (Int.castRingHom κ) (aeval (jqModC ℤ) P) = aeval (jqModC κ) P := by
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
    congr 1
    · exact RingHom.ext_int _ _
    · exact map_jqModC _
  have hmapaeval : aeval (jqModC κ) (P.map (Int.castRingHom κ)) = aeval (jqModC κ) P := by
    rw [aeval_def, Polynomial.eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have hPκ : aeval (jqModC κ) (P.map (Int.castRingHom κ)) =
      ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := by
    rw [hmapaeval, ← haevalκ, ← hxκ', ← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, neg_eq_zero]
    exact hzκ
  set Q : κ[X] := ∏ a ∈ S, (X - C a) ^ (12 / jWidth a) with hQ
  have hQeval : aeval (jqModC κ) Q = ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := by
    rw [hQ, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_pow, map_sub, aeval_X, aeval_C, HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap,
      HahnSeries.ofPowerSeries_C]
  have hinj : Function.Injective (aeval (jqModC κ) : κ[X] →ₐ[κ] LaurentSeries κ) :=
    transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC κ)
  have hPQ : P.map (Int.castRingHom κ) = Q := hinj (hPκ.trans hQeval.symm)
  rw [← hP, Polynomial.map_map, ← hPQ]
  congr 1
  exact RingHom.ext_int _ _

end S_ModularCurve_DRModel_map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet
end P2MW
export P2MW.S_ModularCurve_DRModel_map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet (solution)
