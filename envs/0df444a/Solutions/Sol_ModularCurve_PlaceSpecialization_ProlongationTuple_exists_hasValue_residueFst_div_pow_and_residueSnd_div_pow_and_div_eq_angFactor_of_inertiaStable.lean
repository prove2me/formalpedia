-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1884bb61-a9e2-5ee4-9e29-00e2bcac3f53

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecialization
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_two_le_ringKrullDim_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
import Theorems.Thm_ModularCurve_UVCrossingModel_sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_neg_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_V_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueSnd_div_nodeResidueSnd_x_pow_of_sub_mul_U_pow_mem_of_hasValue
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_length_localizedModule_quotient_map_eq_of_mem_minimalPrimes
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_surjective
import Theorems.Thm_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.UVCrossingModel ModularCurve.NodeLocalized

namespace Ws12NodeTel

section Model

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

noncomputable abbrev endU (e : ℕ) (ab : PowerSeries W × PowerSeries W) : ℤ :=
  sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab)

noncomputable abbrev endV (e : ℕ) (ab : PowerSeries W × PowerSeries W) : ℤ :=
  sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)

noncomputable abbrev lrU (ϖ : W) (e : ℕ) (ab : PowerSeries W × PowerSeries W) : ResidueField W :=
  leadingResidue ϖ (nfCoeff ab (endU e ab))

noncomputable abbrev lrV (ϖ : W) (e : ℕ) (ab : PowerSeries W × PowerSeries W) : ResidueField W :=
  leadingResidue ϖ (nfCoeff ab (endV e ab))

noncomputable def normProd (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e)) : ResidueField W :=
  ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
    (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
    residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
      (Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat

noncomputable def normProdK {k : Type*} [Field k] (ρ : W →+* k) (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e)) : k :=
  ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
    (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
    ρ (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
      (Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat

theorem isUnit_unitPart (ϖ : W) (hϖ : Irreducible ϖ) (a : W) (ha : a ≠ 0) : IsUnit (unitPart ϖ a) := by
  by_contra hu
  have hfin : FiniteMultiplicity ϖ a := FiniteMultiplicity.of_not_isUnit hϖ.not_isUnit ha
  have hmem : unitPart ϖ a ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  refine ⟨c, ?_⟩
  conv_lhs => rw [← pow_multiplicity_mul_unitPart ϖ a, hc]
  rw [pow_succ]; ring

theorem multiplicity_eq_of_eq_pow_mul (ϖ : W) (hϖ : Irreducible ϖ) (a : W) (n : ℕ) (v : W) (hv : IsUnit v)
    (h : a = ϖ ^ n * v) : multiplicity ϖ a = n := by
  apply multiplicity_eq_of_dvd_of_not_dvd
  · exact ⟨v, h⟩
  · rintro ⟨c, hc⟩
    have h2 : ϖ ^ n * v = ϖ ^ n * (ϖ * c) := by rw [← h, hc]; ring
    have h3 : v = ϖ * c := mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) h2
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h3 ▸ hv))

theorem unitPart_eq_of_eq_pow_mul (ϖ : W) (hϖ : Irreducible ϖ) (a : W) (n : ℕ) (v : W) (hv : IsUnit v)
    (h : a = ϖ ^ n * v) : unitPart ϖ a = v := by
  have hm := multiplicity_eq_of_eq_pow_mul ϖ hϖ a n v hv h
  have h1 := pow_multiplicity_mul_unitPart ϖ a
  rw [hm] at h1
  exact mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) (h1.trans h)

theorem eq_pow_mul_unitPart (ϖ a : W) : a = ϖ ^ multiplicity ϖ a * unitPart ϖ a :=
  (pow_multiplicity_mul_unitPart ϖ a).symm

theorem leadingResidue_of_ne_zero (ϖ : W) (a : W) (ha : a ≠ 0) :
    leadingResidue ϖ a = residue W (unitPart ϖ a) := by
  rw [leadingResidue, if_neg ha]

theorem leadingResidue_mul (ϖ : W) (hϖ : Irreducible ϖ) (a b : W) (ha : a ≠ 0) (hb : b ≠ 0) :
    leadingResidue ϖ (a * b) = leadingResidue ϖ a * leadingResidue ϖ b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [leadingResidue_of_ne_zero ϖ _ hab, leadingResidue_of_ne_zero ϖ _ ha, leadingResidue_of_ne_zero ϖ _ hb, ← map_mul]
  congr 1
  apply unitPart_eq_of_eq_pow_mul ϖ hϖ (a * b) (multiplicity ϖ a + multiplicity ϖ b) _
    ((isUnit_unitPart ϖ hϖ a ha).mul (isUnit_unitPart ϖ hϖ b hb))
  conv_lhs => rw [eq_pow_mul_unitPart ϖ a, eq_pow_mul_unitPart ϖ b]
  ring

theorem leadingResidue_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (a : W) (ha : a ≠ 0) :
    leadingResidue ϖ a ≠ 0 := by
  rw [leadingResidue_of_ne_zero ϖ _ ha, Ne, IsLocalRing.residue_eq_zero_iff]
  exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h (isUnit_unitPart ϖ hϖ a ha)

theorem leadingResidue_of_isUnit (ϖ : W) (hϖ : Irreducible ϖ) (a : W) (ha : IsUnit a) :
    leadingResidue ϖ a = residue W a := by
  rw [leadingResidue_of_ne_zero ϖ _ ha.ne_zero]
  congr 1
  exact unitPart_eq_of_eq_pow_mul ϖ hϖ a 0 a ha (by rw [pow_zero, one_mul])

theorem leadingResidue_pow_mul (ϖ : W) (hϖ : Irreducible ϖ) (n : ℕ) (a : W) (ha : a ≠ 0) :
    leadingResidue ϖ (ϖ ^ n * a) = leadingResidue ϖ a := by
  have h0 : ϖ ^ n * a ≠ 0 := mul_ne_zero (pow_ne_zero n hϖ.ne_zero) ha
  rw [leadingResidue_of_ne_zero ϖ _ h0, leadingResidue_of_ne_zero ϖ _ ha]
  congr 1
  apply unitPart_eq_of_eq_pow_mul ϖ hϖ _ (n + multiplicity ϖ a) _ (isUnit_unitPart ϖ hϖ a ha)
  conv_lhs => rw [eq_pow_mul_unitPart ϖ a]
  ring

theorem unitPart_mul_of_isUnit (ϖ : W) (hϖ : Irreducible ϖ) (a v : W) (ha : a ≠ 0) (hv : IsUnit v) :
    unitPart ϖ (a * v) = unitPart ϖ a * v := by
  apply unitPart_eq_of_eq_pow_mul ϖ hϖ _ (multiplicity ϖ a) _ ((isUnit_unitPart ϖ hϖ a ha).mul hv)
  conv_lhs => rw [eq_pow_mul_unitPart ϖ a]
  ring

end Model

section Mono

variable {W : Type u} [CommRing W]

theorem annulusWeight_zero_nfExponent (E : ℕ) (n : ℤ) :
    annulusWeight E 0 (nfExponent n) = (-n).toNat * E := by
  cases n with
  | ofNat i => simp [annulusWeight, nfExponent]
  | negSucc j =>
      simp only [annulusWeight, nfExponent, Finsupp.single_apply]
      simp

theorem annulusWeight_self_nfExponent (E : ℕ) (n : ℤ) :
    annulusWeight E E (nfExponent n) = n.toNat * E := by
  cases n with
  | ofNat i => simp [annulusWeight, nfExponent]
  | negSucc j => simp [annulusWeight, nfExponent]

theorem termOrder_zero_eq (v : W → ℕ∞) (E : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E 0 ab n = v (nfCoeff ab n) + (((-n).toNat * E : ℕ) : ℕ∞) := by
  rw [termOrder, annulusWeight_zero_nfExponent]

theorem termOrder_self_eq (v : W → ℕ∞) (E : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E E ab n = v (nfCoeff ab n) + ((n.toNat * E : ℕ) : ℕ∞) := by
  rw [termOrder, annulusWeight_self_nfExponent]

theorem eq_zero_of_forall_nfCoeff_eq_zero (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (h : ∀ n : ℤ, nfCoeff ab n = 0) :
    inU ab.1 + inV ab.2 = 0 := by
  have ha : ab.1 = 0 := by
    ext i
    have := h (Int.ofNat i)
    simpa [nfCoeff] using this
  have hb' : ab.2 = 0 := by
    ext j
    cases j with
    | zero => simpa using hb
    | succ j =>
        have := h (Int.negSucc j)
        simpa [nfCoeff] using this
  rw [ha, hb']
  ext d
  simp [coeff_inU, coeff_inV]

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem iInf_termOrder_ne_top (π : W) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) :
    (⨅ n : ℤ, termOrder (IsDiscreteValuationRing.addVal W) E t ab n) ≠ ⊤ := by
  intro htop
  apply hx
  rw [eq_zero_of_forall_nfCoeff_eq_zero ab hb ?_, map_zero]
  intro n
  have hn : termOrder (IsDiscreteValuationRing.addVal W) E t ab n = ⊤ :=
    eq_top_iff.mpr (htop ▸ iInf_le _ n)
  by_contra hne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (show IsDiscreteValuationRing.addVal W (nfCoeff ab n) ≠ ⊤ from fun h => hne (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
  rw [termOrder, ← hm, ← ENat.coe_add] at hn
  exact ENat.coe_ne_top _ hn

theorem dominantIndices_nonempty (π : W) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) :
    (dominantIndices (IsDiscreteValuationRing.addVal W) E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ENat.exists_eq_iInf (fun n : ℤ => termOrder (IsDiscreteValuationRing.addVal W) E t ab n)
  refine ⟨n, ?_⟩
  show termOrder _ E t ab n = repGaussOrder _ E t (inU ab.1 + inV ab.2)
  rw [repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E t ab hb]
  exact hn

theorem repGaussOrder_le_termOrder (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    repGaussOrder (IsDiscreteValuationRing.addVal W) E t (inU ab.1 + inV ab.2) ≤
      termOrder (IsDiscreteValuationRing.addVal W) E t ab n := by
  rw [repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E t ab hb]
  exact iInf_le _ n

theorem le_of_mem_dominantIndices (π : W) (E : ℕ) (hE : 1 ≤ E) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hx : mk π (inU ab.1 + inV ab.2) ≠ 0)
    {s t : ℤ} (hs : s ∈ dominantIndices (IsDiscreteValuationRing.addVal W) E 0 ab)
    (ht : t ∈ dominantIndices (IsDiscreteValuationRing.addVal W) E E ab) : t ≤ s := by

  have h0 : termOrder (IsDiscreteValuationRing.addVal W) E 0 ab s ≤ termOrder (IsDiscreteValuationRing.addVal W) E 0 ab t := by
    rw [show termOrder _ E 0 ab s = _ from hs]; exact repGaussOrder_le_termOrder E 0 ab hb t
  have hE' : termOrder (IsDiscreteValuationRing.addVal W) E E ab t ≤ termOrder (IsDiscreteValuationRing.addVal W) E E ab s := by
    rw [show termOrder _ E E ab t = _ from ht]; exact repGaussOrder_le_termOrder E E ab hb s

  have hfin0 := iInf_termOrder_ne_top π E 0 ab hb hx
  have hfinE := iInf_termOrder_ne_top π E E ab hb hx
  have hs_fin : IsDiscreteValuationRing.addVal W (nfCoeff ab s) ≠ ⊤ := by
    intro h
    apply hfin0
    rw [← repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E 0 ab hb, ← hs,
      termOrder, h, top_add]
  have ht_fin : IsDiscreteValuationRing.addVal W (nfCoeff ab t) ≠ ⊤ := by
    intro h
    apply hfinE
    rw [← repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E E ab hb, ← ht,
      termOrder, h, top_add]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hs_fin
  obtain ⟨m', hm'⟩ := ENat.ne_top_iff_exists.mp ht_fin
  rw [termOrder_zero_eq, termOrder_zero_eq, ← hm, ← hm'] at h0
  rw [termOrder_self_eq, termOrder_self_eq, ← hm, ← hm'] at hE'

  have h0' : m + (-s).toNat * E ≤ m' + (-t).toNat * E := by exact_mod_cast h0
  have hE'' : m' + t.toNat * E ≤ m + s.toNat * E := by exact_mod_cast hE'
  have hsum : ((-s).toNat + t.toNat) * E ≤ ((-t).toNat + s.toNat) * E := by nlinarith
  have hkey : (-s).toNat + t.toNat ≤ (-t).toNat + s.toNat := Nat.le_of_mul_le_mul_right hsum hE
  omega

theorem sSup_dominantIndices_le_sInf_dominantIndices [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (nf : PowerSeries W × PowerSeries W)
    (hnf : PowerSeries.constantCoeff nf.2 = 0 ∧ mk (ϖ ^ e) (inU nf.1 + inV nf.2) = x) :
    sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nf) ≤
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nf) := by
  have hx' : mk (ϖ ^ e) (inU nf.1 + inV nf.2) ≠ 0 := by rw [hnf.2]; exact hx
  have hne0 := dominantIndices_nonempty (ϖ ^ e) e 0 nf hnf.1 hx'
  have hneE := dominantIndices_nonempty (ϖ ^ e) e e nf hnf.1 hx'
  refine le_csInf hne0 fun s hs => ?_
  exact csSup_le hneE fun t ht => le_of_mem_dominantIndices (ϖ ^ e) e he nf hnf.1 hx' hs ht

end Mono

section EndsMem
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem endU_mem (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    endU e ab ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab := by
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := by rw [habx]; exact hx
  have hne0 := dominantIndices_nonempty (ϖ ^ e) e 0 ab hb hx'
  obtain ⟨t, ht⟩ := dominantIndices_nonempty (ϖ ^ e) e e ab hb hx'
  exact Int.csInf_mem hne0 ⟨t, fun s hs => le_of_mem_dominantIndices (ϖ ^ e) e he ab hb hx' hs ht⟩

theorem endV_mem (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    endV e ab ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e e ab := by
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := by rw [habx]; exact hx
  have hneE := dominantIndices_nonempty (ϖ ^ e) e e ab hb hx'
  obtain ⟨s, hs⟩ := dominantIndices_nonempty (ϖ ^ e) e 0 ab hb hx'
  exact Int.csSup_mem hneE ⟨s, fun t ht => le_of_mem_dominantIndices (ϖ ^ e) e he ab hb hx' hs ht⟩

theorem nfCoeff_ne_zero_of_mem_dominantIndices (π : W) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) (n : ℤ)
    (hn : n ∈ dominantIndices (IsDiscreteValuationRing.addVal W) E t ab) : nfCoeff ab n ≠ 0 := by
  intro h0
  apply iInf_termOrder_ne_top π E t ab hb hx
  rw [← repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E t ab hb]
  rw [← show termOrder _ E t ab n = _ from hn, termOrder, h0, AddValuation.map_zero, top_add]

end EndsMem

section Model2

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem lrU_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    lrU ϖ e ab'' = lrU ϖ e ab * lrU ϖ e ab' :=
  (leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul ϖ hϖ e he x hx ab hb habx y hy ab' hb' haby ab'' hb'' habxy).1

theorem lrV_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    lrV ϖ e ab'' = lrV ϖ e ab * lrV ϖ e ab' :=
  (leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul ϖ hϖ e he x hx ab hb habx y hy ab' hb' haby ab'' hb'' habxy).2

theorem lrU_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) : lrU ϖ e ab ≠ 0 := by
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := by rw [habx]; exact hx
  exact leadingResidue_ne_zero ϖ hϖ _
    (nfCoeff_ne_zero_of_mem_dominantIndices (ϖ ^ e) e 0 ab hb hx' _ (endU_mem ϖ hϖ e he x hx ab hb habx))

theorem lrV_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) : lrV ϖ e ab ≠ 0 := by
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := by rw [habx]; exact hx
  exact leadingResidue_ne_zero ϖ hϖ _
    (nfCoeff_ne_zero_of_mem_dominantIndices (ϖ ^ e) e e ab hb hx' _ (endV_mem ϖ hϖ e he x hx ab hb habx))

theorem inU_C_add_inV_zero (w₀ : W) :
    inU (PowerSeries.C w₀) + inV (0 : PowerSeries W) = MvPowerSeries.C w₀ := by
  ext d
  rw [map_add, coeff_inU, coeff_inV, MvPowerSeries.coeff_C]
  simp only [map_zero, ite_self, add_zero, PowerSeries.coeff_C]
  by_cases h1 : d 1 = 0
  · by_cases h0 : d 0 = 0
    · have hd : d = 0 := by
        ext i; fin_cases i
        · exact h0
        · exact h1
      simp [h1, h0, hd]
    · have hd : d ≠ 0 := fun hd => h0 (by rw [hd]; rfl)
      simp [h1, h0, hd]
  · have hd : d ≠ 0 := fun hd => h1 (by rw [hd]; rfl)
    simp [h1, hd]

theorem normalForm_const (ϖ : W) (e : ℕ) (w₀ : W) :
    PowerSeries.constantCoeff ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W).2 = 0 ∧
      mk (ϖ ^ e) (inU ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W).1 +
        inV ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W).2) = const (ϖ ^ e) w₀ := by
  refine ⟨map_zero _, ?_⟩
  show mk (ϖ ^ e) (inU (PowerSeries.C w₀) + inV 0) = const (ϖ ^ e) w₀
  rw [inU_C_add_inV_zero]; rfl

theorem nfCoeff_const (w₀ : W) (n : ℤ) :
    nfCoeff ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) n = if n = 0 then w₀ else 0 := by
  cases n with
  | ofNat i =>
    show PowerSeries.coeff i (PowerSeries.C w₀) = _
    rw [PowerSeries.coeff_C]
    by_cases hi : i = 0
    · subst hi; simp
    · have : (Int.ofNat i : ℤ) ≠ 0 := by rw [Int.ofNat_eq_coe]; exact_mod_cast hi
      simp [hi, this]
  | negSucc j =>
    show PowerSeries.coeff (j + 1) (0 : PowerSeries W) = _
    rw [map_zero, if_neg (Int.negSucc_ne_zero j)]

theorem termOrder_const_of_ne_zero (e t : ℕ) (w₀ : W) (n : ℤ) (hn : n ≠ 0) :
    termOrder (IsDiscreteValuationRing.addVal W) e t ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) n = ⊤ := by
  rw [termOrder, nfCoeff_const, if_neg hn, AddValuation.map_zero, top_add]

theorem termOrder_const_zero (e t : ℕ) (w₀ : W) :
    termOrder (IsDiscreteValuationRing.addVal W) e t ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) 0 =
      IsDiscreteValuationRing.addVal W w₀ := by
  rw [termOrder, nfCoeff_const, if_pos rfl]
  have : annulusWeight e t (nfExponent 0) = 0 := by
    show annulusWeight e t (Finsupp.single 0 0) = 0
    simp [annulusWeight]
  rw [this, Nat.cast_zero, add_zero]

theorem dominantIndices_const (e t : ℕ) (w₀ : W) (hw₀ : w₀ ≠ 0) :
    dominantIndices (IsDiscreteValuationRing.addVal W) e t ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) = {0} := by
  have hrep : repGaussOrder (IsDiscreteValuationRing.addVal W) e t
      (inU ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W).1 + inV ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W).2) =
      IsDiscreteValuationRing.addVal W w₀ := by
    rw [repGaussOrder_normalForm_eq_iInf_termOrder _ (AddValuation.map_zero _) e t _ (map_zero _)]
    apply le_antisymm
    · exact (iInf_le _ 0).trans (termOrder_const_zero e t w₀).le
    · refine le_iInf fun n => ?_
      by_cases hn : n = 0
      · subst hn; exact (termOrder_const_zero e t w₀).ge
      · rw [termOrder_const_of_ne_zero e t w₀ n hn]; exact le_top
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq, Set.mem_singleton_iff, hrep]
  constructor
  · intro h
    by_contra hn
    rw [termOrder_const_of_ne_zero e t w₀ n hn] at h
    exact (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hw₀) h.symm
  · rintro rfl; exact termOrder_const_zero e t w₀

theorem endU_const (e : ℕ) (he : 1 ≤ e) (w₀ : W) (hw₀ : w₀ ≠ 0) :
    endU e ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) = 0 := by
  show sInf _ = 0
  rw [dominantIndices_const e 0 w₀ hw₀, csInf_singleton]

theorem endV_const (e : ℕ) (he : 1 ≤ e) (w₀ : W) (hw₀ : w₀ ≠ 0) :
    endV e ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) = 0 := by
  show sSup _ = 0
  rw [dominantIndices_const e e w₀ hw₀, csSup_singleton]

theorem lrU_const (ϖ : W) (e : ℕ) (he : 1 ≤ e) (w₀ : W) (hw₀ : w₀ ≠ 0) :
    lrU ϖ e ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) = leadingResidue ϖ w₀ := by
  show leadingResidue ϖ (nfCoeff _ (endU e _)) = _
  rw [endU_const e he w₀ hw₀, nfCoeff_const, if_pos rfl]

theorem lrV_const (ϖ : W) (e : ℕ) (he : 1 ≤ e) (w₀ : W) (hw₀ : w₀ ≠ 0) :
    lrV ϖ e ((PowerSeries.C w₀, 0) : PowerSeries W × PowerSeries W) = leadingResidue ϖ w₀ := by
  show leadingResidue ϖ (nfCoeff _ (endV e _)) = _
  rw [endV_const e he w₀ hw₀, nfCoeff_const, if_pos rfl]

theorem inU_zero_add_inV_zero : inU (0 : PowerSeries W) + inV (0 : PowerSeries W) = 0 := by
  ext d
  rw [map_add, coeff_inU, coeff_inV]
  simp

theorem const_eq_zero_imp (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (w₀ : W)
    (h : const (ϖ ^ e) w₀ = 0) : w₀ = 0 := by
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hϖ.maximalIdeal_eq ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  have h1 := normalForm_const ϖ e w₀
  have h0 : PowerSeries.constantCoeff ((0, 0) : PowerSeries W × PowerSeries W).2 = 0 ∧
      mk (ϖ ^ e) (inU ((0, 0) : PowerSeries W × PowerSeries W).1 + inV ((0, 0) : PowerSeries W × PowerSeries W).2) =
        const (ϖ ^ e) w₀ := by
    refine ⟨map_zero _, ?_⟩
    rw [h]
    show mk (ϖ ^ e) (inU 0 + inV 0) = 0
    rw [inU_zero_add_inV_zero, map_zero]
  have h2 := (existsUnique_normalForm ϖ e he (const (ϖ ^ e) w₀)).unique h1 h0
  have h3 := congrArg (fun ab : PowerSeries W × PowerSeries W => PowerSeries.constantCoeff ab.1) h2
  simpa using h3

theorem const_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (w₀ : W) (hw₀ : w₀ ≠ 0) :
    const (ϖ ^ e) w₀ ≠ 0 := fun h => hw₀ (const_eq_zero_imp ϖ hϖ e he w₀ h)

theorem U_mul_V_eq (π : W) (E : ℕ) : U (π ^ E) * V (π ^ E) = const (π ^ E) π ^ E := by
  rw [← constHom_apply, ← map_pow, constHom_apply]
  show mk (π ^ E) (MvPowerSeries.X 0) * mk (π ^ E) (MvPowerSeries.X 1) = mk (π ^ E) (MvPowerSeries.C (π ^ E))
  rw [← map_mul]
  apply (Ideal.Quotient.eq).mpr
  exact Ideal.subset_span rfl

theorem isUnit_constantCoeff_of_isUnit_mk (π : W) (E : ℕ) (hE : 1 ≤ E) (hπ : ¬ IsUnit π)
    (G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk (π ^ E) G)) : IsUnit (MvPowerSeries.constantCoeff G) := by
  obtain ⟨y, hy⟩ := hG.exists_right_inv
  obtain ⟨G', rfl⟩ := mk_surjective (π ^ E) y
  rw [← map_mul, ← (mk (π ^ E)).map_one, eq_comm] at hy
  have hmem := (Ideal.Quotient.eq).mp hy
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨H, hH⟩ := hmem
  have h0 := congrArg MvPowerSeries.constantCoeff hH
  simp only [map_sub, map_one, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C,
    zero_sub] at h0

  have h1 : MvPowerSeries.constantCoeff G * MvPowerSeries.constantCoeff G' = 1 + π ^ E * MvPowerSeries.constantCoeff H := by
    linear_combination -h0
  have hu : IsUnit (1 + π ^ E * MvPowerSeries.constantCoeff H) := by
    have hmem : π ^ E * MvPowerSeries.constantCoeff H ∈ maximalIdeal W :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hπ) E hE)
    have hneg : -(π ^ E * MvPowerSeries.constantCoeff H) ∈ nonunits W := by
      rw [← IsLocalRing.mem_maximalIdeal]; exact neg_mem hmem
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hneg
    rwa [sub_neg_eq_add] at this
  rw [← h1] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem apply_constantCoeff_eq_of_sub_mem_span {k : Type*} [Field k] (ρ : W →+* k) (π : W) (E : ℕ) (hE : 1 ≤ E)
    (hρπ : ρ π = 0) (G G' : MvPowerSeries (Fin 2) W) (Z : UVCrossingModel W (π ^ E))
    (hZ : Z = U (π ^ E) ∨ Z = V (π ^ E))
    (h : mk (π ^ E) G - mk (π ^ E) G' ∈ Ideal.span {const (π ^ E) π, Z}) :
    ρ (MvPowerSeries.constantCoeff G) = ρ (MvPowerSeries.constantCoeff G') := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  obtain ⟨A, rfl⟩ := mk_surjective (π ^ E) a
  obtain ⟨B, rfl⟩ := mk_surjective (π ^ E) b
  obtain ⟨i, hZi⟩ : ∃ i : Fin 2, Z = mk (π ^ E) (MvPowerSeries.X i) := by
    rcases hZ with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  rw [hZi] at hab
  have hmem : G - G' - (A * MvPowerSeries.C π + B * MvPowerSeries.X i) ∈ uvCrossingIdeal W (π ^ E) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show mk (π ^ E) (G - G' - (A * MvPowerSeries.C π + B * MvPowerSeries.X i)) = 0
    rw [map_sub, map_sub, map_add, map_mul, map_mul, ← hab]
    show _ - (mk (π ^ E) A * mk (π ^ E) (MvPowerSeries.C π) + _) = 0
    exact sub_self _
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨H, hH⟩ := hmem
  have h0 := congrArg MvPowerSeries.constantCoeff hH
  simp only [map_sub, map_add, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, mul_zero,
    zero_sub, add_zero] at h0

  have h1 : MvPowerSeries.constantCoeff G - MvPowerSeries.constantCoeff G' =
      MvPowerSeries.constantCoeff A * π - MvPowerSeries.constantCoeff H * π ^ E := by
    linear_combination -h0
  rw [← sub_eq_zero, ← map_sub, h1, map_sub, map_mul, map_mul, map_pow, hρπ, mul_zero, zero_pow (by omega), mul_zero,
    sub_self]

theorem one_mul_addVal :
    (fun w : W => (1 : ℕ∞) * IsDiscreteValuationRing.addVal W w) = (IsDiscreteValuationRing.addVal W : W → ℕ∞) := by
  funext w; exact one_mul _

theorem endV_eq_and_lrV_eq_of_sub_mul_V_pow_mem (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (n : ℕ)
    (hxγ : x - γ * V (ϖ ^ e) ^ n ∈ Ideal.span {const (ϖ ^ e) ϖ, U (ϖ ^ e)})
    (G : MvPowerSeries (Fin 2) W) (hG : mk (ϖ ^ e) G = γ) :
    endV e ab = -(n : ℤ) ∧ lrV ϖ e ab = residue W (MvPowerSeries.constantCoeff G) := by
  have h1 := sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem ϖ hϖ e he 1 le_rfl x hx ab hb habx γ hγ n hxγ
  have h2 := leadingResidue_nfCoeff_neg_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_V_pow_mem
    ϖ hϖ e he 1 le_rfl x hx ab hb habx γ hγ n hxγ G hG
  simp only [one_mul_addVal, Nat.cast_one, one_mul] at h1 h2
  refine ⟨h1.2, ?_⟩
  show leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) = _
  rw [h1.2]; exact h2.1

theorem endU_eq_and_lrU_eq_of_sub_mul_U_pow_mem (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
    (hxγ : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)})
    (G : MvPowerSeries (Fin 2) W) (hG : mk (ϖ ^ e) G = γ) :
    endU e ab = (m : ℤ) ∧ lrU ϖ e ab = residue W (MvPowerSeries.constantCoeff G) := by
  have h1 := sInf_dominantIndices_eq_of_sub_mul_U_pow_mem ϖ hϖ e he 1 le_rfl x hx ab hb habx γ hγ m hxγ
  have h2 := leadingResidue_nfCoeff_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_U_pow_mem
    ϖ hϖ e he 1 le_rfl x hx ab hb habx γ hγ m hxγ G hG
  simp only [one_mul_addVal, Nat.cast_one, one_mul] at h1 h2
  refine ⟨h1.2, ?_⟩
  show leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) = _
  rw [h1.2]; exact h2.1

theorem lrV_mul_normProd_eq (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    lrV ϖ e ab * normProd ϖ e x = (-1) ^ (endU e ab - endV e ab).toNat * lrU ϖ e ab :=
  leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq ϖ hϖ e he x hx ab hb habx

theorem endU_sub_endV_eq_finsum (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    0 ≤ endU e ab - endV e ab ∧
    (((endU e ab - endV e ab).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (_ : P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal),
        (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ P.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime P.asIdeal)
            (LocalizedModule P.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) := by
  have hmono := sSup_dominantIndices_le_sInf_dominantIndices ϖ hϖ e he x hx ab ⟨hb, habx⟩
  refine ⟨sub_nonneg.mpr hmono, ?_⟩
  have h := finsum_rank_mul_length_eq_sInf_sub_sSup ϖ hϖ e he 1 le_rfl x hx ab hb habx
  simp only [one_mul_addVal, Nat.cast_one, one_mul] at h
  exact h.symm

theorem lift_normProd {k : Type*} [Field k] (ρ : W →+* k) [IsLocalHom ρ] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) :
    IsLocalRing.ResidueField.lift ρ (normProd ϖ e x) = normProdK ρ ϖ e x := by
  classical
  have hfin : {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal}.Finite :=
    setOf_horizontal_mem_finite ϖ hϖ e he x hx
  simp only [normProd, normProdK]
  rw [show (fun Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) => ∏ᶠ (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
      residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
        (Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat) =
      fun Q => ∏ᶠ (_ : Q ∈ hfin.toFinset), residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
        (Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat
      from funext fun Q => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]]
  rw [show (fun Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) => ∏ᶠ (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
      ρ (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
        (Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat) =
      fun Q => ∏ᶠ (_ : Q ∈ hfin.toFinset), ρ (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
        (Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat
      from funext fun Q => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]]
  rw [finprod_mem_finset_eq_prod, finprod_mem_finset_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun Q _ => ?_
  rw [map_pow, IsLocalRing.ResidueField.lift_residue_apply]

end Model2

section Branches

variable {R : Type u} [CommRing R]

theorem false_of_lt_lt_of_ringKrullDim_le_two [IsLocalRing R] (hR : ringKrullDim R ≤ 2)
    {P Q : Ideal R} [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : (⊥ : Ideal R) < P) (hbot : (⊥ : Ideal R).IsPrime)
    (hPQ : P < Q) (hQm : Q < maximalIdeal R) : False := by
  let s : LTSeries (PrimeSpectrum R) :=
    { length := 3
      toFun := ![⟨⊥, hbot⟩, ⟨P, hP⟩, ⟨Q, hQ⟩, ⟨maximalIdeal R, inferInstance⟩]
      step := by
        intro i
        fin_cases i
        · exact hP0
        · exact hPQ
        · exact hQm }
  have h := Order.LTSeries.length_le_krullDim s
  have h3 : ((3 : ℕ) : WithBot ℕ∞) ≤ 2 := h.trans hR
  have : (3 : ℕ) ≤ 2 := by
    have h3' : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := h3
    have h3'' : (3 : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h3'
    exact_mod_cast h3''
  omega

theorem mem_minimalPrimes_of_ne_bot [IsDomain R] [IsLocalRing R] (hR : ringKrullDim R ≤ 2)
    (I : Ideal R) (hI : I ≠ ⊥) (Q : Ideal R) [hQ : Q.IsPrime] (hIQ : I ≤ Q) (hQm : Q ≠ maximalIdeal R) :
    Q ∈ I.minimalPrimes := by
  refine ⟨⟨hQ, hIQ⟩, ?_⟩
  rintro P ⟨hP, hIP⟩ hPQ
  haveI := hP
  by_contra hQP
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hQP (h ▸ le_rfl))
  have hP0 : (⊥ : Ideal R) < P := bot_lt_iff_ne_bot.mpr (fun h => hI (le_bot_iff.mp (h ▸ hIP)))
  have hQm' : Q < maximalIdeal R := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) hQm
  exact false_of_lt_lt_of_ringKrullDim_le_two hR hP0 Ideal.bot_prime hlt hQm'

theorem ne_bot_and_comap_eq_of_map_le
    {B : Type*} [CommRing B] [IsLocalRing B] [IsDomain R]
    (j : B →+* R) (hj : Function.Injective j)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (𝔮 : Ideal B) [𝔮.IsPrime] (f : B) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (Q : Ideal R) [Q.IsPrime] (hJQ : Ideal.map j 𝔮 ≤ Q) (hQm : ∃ b ∈ maximalIdeal B, j b ∉ Q) :
    Q ≠ ⊥ ∧ Q.comap j = 𝔮 := by
  have hjf : j f ∈ Q := hJQ (Ideal.mem_map_of_mem j hf𝔮)
  refine ⟨fun hQ => hf (hj ?_), ?_⟩
  · rw [map_zero]
    rw [hQ] at hjf
    exact (Ideal.mem_bot.mp hjf)
  · have hle : 𝔮 ≤ Q.comap j := Ideal.le_comap_of_map_le hJQ
    haveI : (Q.comap j).IsPrime := Ideal.IsPrime.comap j
    have hne : Q.comap j ≠ maximalIdeal B := by
      obtain ⟨b, hb, hbQ⟩ := hQm
      intro h
      exact hbQ (show b ∈ Q.comap j from h ▸ hb)
    by_contra hneq
    have hlt : 𝔮 < Q.comap j := lt_of_le_of_ne hle (Ne.symm hneq)
    have := hht 𝔮 (Q.comap j) inferInstance inferInstance hne hlt
    exact hf (by rw [this] at hf𝔮; exact (Ideal.mem_bot.mp hf𝔮))

theorem length_localizedModule_quotient_eq_zero (x : R) (Q : Ideal R) [Q.IsPrime]
    (hx : x ∉ Q) : Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ Ideal.span {x})) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine subsingleton_of_forall_eq 0 fun m => ?_
  induction m using LocalizedModule.induction_on with
  | h a s =>
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [Submonoid.smul_def, smul_zero]
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)

end Branches

section C2A
open Valued

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_mem_and_red_eq_of_coe_eq_coe_adicCompletion
    {L : Type u} [Field L] (A : ValuationSubring L) {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (O : Subring L) (hOA : O ≤ A.toSubring) [IsDiscreteValuationRing O]
    (ϖ : O) (hϖgen : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (hϖ0 : (ϖ : L) ≠ 0)
    (hredϖ : red ⟨(ϖ : L), hOA ϖ.2⟩ = 0)
    {W : Type*} [CommRing W] [IsLocalRing W]
    (τ : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+* W) (ρ : W →+* k)
    (hρ : ∀ o : O, ρ (τ (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o)) = red ⟨(o : L), hOA o.2⟩)
    (j : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* 𝒪[(A.valuation).Completion])
    (hj : ∀ o : O, ((j (algebraMap O _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ((o : L) : (A.valuation).Completion))
    (𝕌 : W) (z : L)
    (hz : ((z : L) : (A.valuation).Completion) = ((j (τ.symm 𝕌) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) :
    ∃ hmem : z ∈ A, red ⟨z, hmem⟩ = ρ 𝕌 := by
  classical

  have hϖC : ((ϖ : L) : (A.valuation).Completion) ≠ 0 := by
    intro h
    have hv := Valued.valuedCompletion_apply (K := WithVal A.valuation) ((WithVal.equiv A.valuation).symm (ϖ : L))
    rw [h, map_zero] at hv
    exact ((Valuation.ne_zero_iff A.valuation).mpr hϖ0) hv.symm

  set ŵ := τ.symm 𝕌 with hŵ
  have hFG : (IsLocalRing.maximalIdeal O).FG := IsNoetherian.noetherian _
  obtain ⟨o, y, hy, hŵeq⟩ := AdicCompletion.exists_eq_algebraMap_add (IsLocalRing.maximalIdeal O) hFG 1 ŵ
  rw [pow_one] at hy
  have hy' : y ∈ (Ideal.span {ϖ}).map (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O)) := by
    rw [← hϖgen]; exact hy
  rw [Ideal.map_span, Set.image_singleton] at hy'
  obtain ⟨y', rfl⟩ := Ideal.mem_span_singleton'.mp hy'

  have hzC : ((z : L) : (A.valuation).Completion)
      = ((o : L) : (A.valuation).Completion) + ((ϖ : L) : (A.valuation).Completion)
          * ((j y' : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
    rw [hz, hŵeq, map_add, map_mul, Subring.coe_add, Subring.coe_mul, hj o, hj ϖ, mul_comm]

  set t : L := (z - (o : L)) / (ϖ : L) with ht
  have htz : z = (o : L) + (ϖ : L) * t := by
    rw [ht, mul_div_cancel₀ _ hϖ0]; ring
  have hmul : (ϖ : L) * t = z - (o : L) := by rw [htz]; ring
  have key : ((ϖ : L) : (A.valuation).Completion) * ((t : L) : (A.valuation).Completion)
      = ((z : L) : (A.valuation).Completion) - ((o : L) : (A.valuation).Completion) := by
    rw [← UniformSpace.Completion.coe_mul, ← UniformSpace.Completion.coe_sub, ← map_mul, ← map_sub, hmul]
  have htC : ((t : L) : (A.valuation).Completion) = ((j y' : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
    apply mul_left_cancel₀ hϖC
    rw [key, hzC, add_sub_cancel_left]
  have htv : A.valuation t ≤ 1 := by
    have hmem := (Valuation.mem_integer_iff _ _).mp (j y').2
    rw [← htC, Valued.valuedCompletion_apply] at hmem
    exact hmem
  have htA : t ∈ A := (A.valuation_le_one_iff t).mp htv
  have hzA : z ∈ A := by
    rw [htz]; exact add_mem (hOA o.2) (mul_mem (hOA ϖ.2) htA)
  refine ⟨hzA, ?_⟩
  have hz' : (⟨z, hzA⟩ : A) = ⟨(o : L), hOA o.2⟩ + ⟨(ϖ : L), hOA ϖ.2⟩ * ⟨t, htA⟩ :=
    Subtype.ext (by simpa using htz)
  have h𝕌 : 𝕌 = τ ŵ := by rw [hŵ, RingEquiv.apply_symm_apply]
  rw [hz', map_add, map_mul, hredϖ, zero_mul, add_zero, h𝕌, hŵeq, map_add, map_add, map_mul, map_mul, hρ o, hρ ϖ,
    hredϖ, mul_zero, add_zero]

end C2A

section FinalIdentity

theorem nodeTel_final_identity {k : Type*} [Field k]
    (ra₁ rb₁ ra₂ rb₂ rα rβ ua₁ ub₁ nPa nPb ηbar₁ ηbar₂ Θ εbar u0 : k)
    (hrb₁ : rb₁ ≠ 0) (hra₂ : ra₂ ≠ 0) (hrb₂ : rb₂ ≠ 0) (hrα : rα ≠ 0) (hrβ : rβ ≠ 0)
    (hua₁ : ua₁ ≠ 0) (hub₁ : ub₁ ≠ 0) (hnPa : nPa ≠ 0) (hnPb : nPb ≠ 0)
    (hη₁ : ηbar₁ ≠ 0) (hη₂ : ηbar₂ ≠ 0) (hΘ : Θ ≠ 0) (hε : εbar ≠ 0)
    (hA hB na nb ma mb : ℕ) (o₁ o₂ m : ℤ)
    (hF1 : ua₁ * rb₂ * ηbar₂ = ra₂ * ub₁ * ηbar₁)
    (hF2a : ra₁ * nPa = (-1) ^ hA * ua₁)
    (hF2b : rb₁ * nPb = (-1) ^ hB * ub₁)
    (hF4 : Θ * (nPa * rβ ^ hA) = εbar ^ m * (nPb * rβ ^ hB))
    (hdeg : o₁ + o₂ = (hA : ℤ) - (hB : ℤ)) (ho₁ : o₁ = (na : ℤ) - (nb : ℤ)) (ho₂ : o₂ = (ma : ℤ) - (mb : ℤ))
    (hu0 : u0 = rα * rβ) :
    ra₁ * rβ⁻¹ ^ na * (rb₁ * rβ⁻¹ ^ nb)⁻¹ / (ra₂ * rα⁻¹ ^ ma * (rb₂ * rα⁻¹ ^ mb)⁻¹) =
      ηbar₁ / ηbar₂ * (-1) ^ (o₁ + o₂) * u0 ^ o₂ * εbar ^ (-m) * Θ := by
  subst hu0
  have h1 : (-1 : k) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hs2 : ((-1 : k) ^ hA) * ((-1 : k) ^ hA) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have ht2 : ((-1 : k) ^ hB) * ((-1 : k) ^ hB) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have htinv : ((-1 : k) ^ hB)⁻¹ = (-1) ^ hB := by rw [← inv_pow, inv_neg, inv_one]
  have hE : εbar ^ m ≠ 0 := zpow_ne_zero _ hε

  have hua : ua₁ = (-1) ^ hA * (ra₁ * nPa) := by linear_combination (-(-1) ^ hA) * hF2a - ua₁ * hs2
  have hub : ub₁ = (-1) ^ hB * (rb₁ * nPb) := by linear_combination (-(-1) ^ hB) * hF2b - ub₁ * ht2
  rw [hua, hub] at hF1
  have key : (-1) ^ hA * ra₁ * rb₂ * ηbar₂ * εbar ^ m * rβ ^ hB * nPa
      = (-1) ^ hB * ra₂ * rb₁ * ηbar₁ * Θ * rβ ^ hA * nPa := by
    linear_combination (εbar ^ m * rβ ^ hB) * hF1 - ((-1) ^ hB * ra₂ * rb₁ * ηbar₁) * hF4
  have key' : (-1) ^ hA * ra₁ * rb₂ * ηbar₂ * εbar ^ m * rβ ^ hB = (-1) ^ hB * ra₂ * rb₁ * ηbar₁ * Θ * rβ ^ hA :=
    mul_right_cancel₀ hnPa key

  have hexp : ((ma : ℤ) - mb) = ((nb : ℤ) - na) + ((hA : ℤ) - hB) := by omega
  rw [show o₁ + o₂ = (hA : ℤ) - hB from hdeg, ho₂, zpow_sub₀ h1, zpow_natCast, zpow_natCast,
    div_eq_mul_inv ((-1 : k) ^ hA), htinv, mul_zpow, zpow_neg]
  have L : ra₁ * rβ⁻¹ ^ na * (rb₁ * rβ⁻¹ ^ nb)⁻¹ / (ra₂ * rα⁻¹ ^ ma * (rb₂ * rα⁻¹ ^ mb)⁻¹)
      = (ra₁ * rb₂) / (rb₁ * ra₂) * rβ ^ ((nb : ℤ) - na) * rα ^ ((ma : ℤ) - mb) := by
    simp only [inv_pow]
    rw [zpow_sub₀ hrβ, zpow_sub₀ hrα, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
    field_simp
  rw [L]
  have hsplit : rβ ^ ((ma : ℤ) - mb) = rβ ^ ((nb : ℤ) - na) * (rβ ^ hA / rβ ^ hB) := by
    rw [hexp, zpow_add₀ hrβ, zpow_sub₀ hrβ (hA : ℤ) (hB : ℤ), zpow_natCast, zpow_natCast]
  rw [hsplit]
  have hX : rβ ^ ((nb : ℤ) - na) ≠ 0 := zpow_ne_zero _ hrβ
  have hY : rα ^ ((ma : ℤ) - mb) ≠ 0 := zpow_ne_zero _ hrα
  generalize rβ ^ ((nb : ℤ) - na) = X at hX ⊢
  generalize rα ^ ((ma : ℤ) - mb) = Y at hY ⊢
  generalize εbar ^ m = E at hE key' ⊢
  have hpA : rβ ^ hA ≠ 0 := pow_ne_zero _ hrβ
  have hpB : rβ ^ hB ≠ 0 := pow_ne_zero _ hrβ
  field_simp
  linear_combination ((-1) ^ hA) * key' - (ra₁ * rb₂ * ηbar₂ * E * rβ ^ hB) * hs2

end FinalIdentity

section ThetaExponent

theorem theta_exponent_identity {L : Type*} [Field L] (Pa Pb p e : L) (hPa : Pa ≠ 0) (hp : p ≠ 0) (he : e ≠ 0)
    (eK sa sb mp mn : ℕ) (m : ℤ) (hm : m = (mp : ℤ) - (mn : ℤ)) :
    Pb / Pa * (p ^ eK * e) ^ m * (Pa * (p ^ sa)⁻¹) * e ^ mn = p ^ ((eK : ℤ) * m - sa + sb) * (Pb * (p ^ sb)⁻¹ * e ^ mp) := by
  subst hm
  have h1 : (p ^ eK * e) ^ ((mp : ℤ) - mn) = p ^ ((eK : ℤ) * (mp - mn)) * e ^ ((mp : ℤ) - mn) := by
    rw [mul_zpow, ← zpow_natCast p eK, ← zpow_mul]
  have h2 : (p ^ sa)⁻¹ = p ^ (-(sa : ℤ)) := by rw [← zpow_natCast, zpow_neg]
  have h3 : (p ^ sb)⁻¹ = p ^ (-(sb : ℤ)) := by rw [← zpow_natCast, zpow_neg]
  rw [h1, h2, h3, ← zpow_natCast e mn, ← zpow_natCast e mp,
    show (eK : ℤ) * ((mp : ℤ) - mn) - sa + sb = (eK : ℤ) * ((mp : ℤ) - mn) + (-(sa : ℤ)) + sb by ring,
    zpow_add₀ hp, zpow_add₀ hp]
  have hC : p ^ (sb : ℤ) * p ^ (-(sb : ℤ)) = 1 := by rw [← zpow_add₀ hp, add_neg_cancel, zpow_zero]
  have hF : e ^ ((mp : ℤ) - mn) * e ^ (mn : ℤ) = e ^ (mp : ℤ) := by rw [← zpow_add₀ he, sub_add_cancel]
  have hA : p ^ ((eK : ℤ) * ((mp : ℤ) - mn)) ≠ 0 := zpow_ne_zero _ hp
  generalize p ^ ((eK : ℤ) * ((mp : ℤ) - mn)) = A at hA ⊢
  generalize p ^ (-(sa : ℤ)) = B
  generalize p ^ (sb : ℤ) = C at hC ⊢
  generalize p ^ (-(sb : ℤ)) = C' at hC ⊢
  generalize e ^ ((mp : ℤ) - mn) = F at hF ⊢
  generalize e ^ (mn : ℤ) = G at hF ⊢
  generalize e ^ (mp : ℤ) = H at hF ⊢
  field_simp
  linear_combination (-(Pb * B * H)) * hC + (Pb * B) * hF

end ThetaExponent

section Tuple

open Valued

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

theorem isUnit_coeffSubring_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (d : ↥(coeffSubring A K)) :
    IsUnit d ↔ IsUnit (⟨(d : AlgebraicClosure ℚ), d.2.1⟩ : A) := by
  constructor
  · intro h
    exact h.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring))
  · intro h
    have hd0 : (d : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by
      apply h.ne_zero; exact Subtype.ext h0
    have hinvA : (d : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      obtain ⟨e, he⟩ := h.exists_right_inv
      have : (e : AlgebraicClosure ℚ) = (d : AlgebraicClosure ℚ)⁻¹ := by
        have h1 : (d : AlgebraicClosure ℚ) * (e : AlgebraicClosure ℚ) = 1 := by
          have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) he
          simpa using this
        exact (eq_inv_of_mul_eq_one_right h1)
      rw [← this]; exact e.2
    have hinvK : (d : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem d.2.2
    refine ⟨⟨d, ⟨(d : AlgebraicClosure ℚ)⁻¹, hinvA, hinvK⟩, Subtype.ext (mul_inv_cancel₀ hd0),
      Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩

theorem irreducible_of_redRestrict (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing ↥(coeffSubring A K)]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    Irreducible ϖ := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext d
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton', isUnit_coeffSubring_iff,
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← red_eq_zero_iff R]
  change redRestrict red K d = 0 ↔ _
  rw [hϖ]
  constructor
  · rintro ⟨d', rfl⟩; exact ⟨d', mul_comm _ _⟩
  · rintro ⟨d', rfl⟩; exact ⟨d', mul_comm _ _⟩

def enlargeCoordinates (R : ProlongationTuple P) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x.1, hBB' c.x.2⟩
  y := ⟨c.y.1, hBB' c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

theorem not_isStrictFst_and_not_isStrictSnd_of_reduceFst_eq [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hwss : w ∈ ssPlaces q N k)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  have hfix := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w hwss
  constructor
  · intro h; exact h.2 (by rw [hV]; exact hfix)
  · intro h; exact (not_fixed_reduceFst_of_isStrictSnd P V h) (by rw [hV]; exact hfix)

theorem exists_place_reduceFst_eq [IsAlgClosed k] [DecidableEq k] (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (w : Place k (modularFunctionFieldC k N)) (hwss : w ∈ ssPlaces q N k) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w :=
  ModularCurve.PlaceSpecialization.reduceFst_surjective P w

section SepGlue

theorem isRational_of_place (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : V.IsRational := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
  exact (AlgebraicCurve.Place.isRational_iff_deg_eq_one V).2 (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed V)

theorem evalAt_eq_zero_iff (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ V.toValuationSubring) :
    V.evalAt f = 0 ↔ V.toValuationSubring.valuation f < 1 := by
  have hV := isRational_of_place V
  rw [show (f : ↥(modularFunctionFieldBar (N * q))) = ((⟨f, hf⟩ : V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q))) from rfl,
    ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, ← V.algebraMap_evalAt hV hf,
    map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective]

end SepGlue

end Tuple

section Bookkeeping

variable {α β : Type*}

theorem sum_filter_support_eq_sum_filter [DecidableEq β] (X : α →₀ ℤ) (r : α → β) (w : β)
    (S : Finset α) (hS : X.support ⊆ S) :
    (∑ a ∈ X.support with r a = w, X a) = ∑ a ∈ S with r a = w, X a := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hS)
  intro a ha hna
  rw [Finset.mem_filter] at ha
  by_contra h
  exact hna (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, ha.2⟩)

theorem sum_filter_support_eq_sub [DecidableEq β] (D Dg Dh : α →₀ ℤ) (hD : ∀ a, D a = Dh a - Dg a)
    (r : α → β) (w : β) :
    (∑ a ∈ D.support with r a = w, D a) =
      (∑ a ∈ Dh.support with r a = w, Dh a) - ∑ a ∈ Dg.support with r a = w, Dg a := by
  classical
  set S := D.support ∪ Dg.support ∪ Dh.support with hSdef
  rw [sum_filter_support_eq_sum_filter D r w S (by rw [hSdef]; exact Finset.subset_union_left.trans Finset.subset_union_left),
    sum_filter_support_eq_sum_filter Dg r w S (by rw [hSdef]; exact Finset.subset_union_right.trans Finset.subset_union_left),
    sum_filter_support_eq_sum_filter Dh r w S (by rw [hSdef]; exact Finset.subset_union_right),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => hD a

theorem prod_filter_support_eq_prod_filter {M : Type*} [CommGroupWithZero M] [DecidableEq β] (X : α →₀ ℤ) (r : α → β) (w : β)
    (y : α → M) (S : Finset α) (hS : X.support ⊆ S) :
    (∏ a ∈ X.support with r a = w, y a ^ X a) = ∏ a ∈ S with r a = w, y a ^ X a := by
  classical
  apply Finset.prod_subset (Finset.filter_subset_filter _ hS)
  intro a ha hna
  rw [Finset.mem_filter] at ha
  have : X a = 0 := by
    by_contra h
    exact hna (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, ha.2⟩)
  rw [this, zpow_zero]

theorem prod_filter_support_zpow_neg_eq_div {M : Type*} [CommGroupWithZero M] [DecidableEq β] (D Dg Dh : α →₀ ℤ)
    (hD : ∀ a, D a = Dh a - Dg a) (r : α → β) (w : β) (y : α → M) (hy : ∀ a, r a = w → y a ≠ 0) :
    (∏ a ∈ D.support with r a = w, y a ^ (-(D a))) =
      (∏ a ∈ Dg.support with r a = w, y a ^ Dg a) / ∏ a ∈ Dh.support with r a = w, y a ^ Dh a := by
  classical
  set S := D.support ∪ Dg.support ∪ Dh.support with hSdef
  have hnegD : (∏ a ∈ D.support with r a = w, y a ^ (-(D a))) = ∏ a ∈ (-D).support with r a = w, y a ^ ((-D) a) := by
    rw [Finsupp.support_neg]; rfl
  rw [hnegD,
    prod_filter_support_eq_prod_filter (-D) r w y S (by rw [Finsupp.support_neg, hSdef]; exact Finset.subset_union_left.trans Finset.subset_union_left),
    prod_filter_support_eq_prod_filter Dg r w y S (by rw [hSdef]; exact Finset.subset_union_right.trans Finset.subset_union_left),
    prod_filter_support_eq_prod_filter Dh r w y S (by rw [hSdef]; exact Finset.subset_union_right),
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Finset.mem_filter] at ha
  rw [Finsupp.neg_apply, hD a, neg_sub, zpow_sub₀ (hy a ha.2)]

end Bookkeeping

section Places2
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, Place.coe_algebraMap] at h

theorem ord_eq_ord_sub_ord_of_smul_mul_eq (f b a : F) (c : K) (hc : c ≠ 0) (hf : f ≠ 0) (hb : b ≠ 0)
    (hrel : c • f * b = a) (V : Place K F) : V.ord f = V.ord a - V.ord b := by
  rw [← hrel, Algebra.smul_def, V.ord_mul (mul_ne_zero ((map_ne_zero _).mpr hc) hf) hb,
    V.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap']
  ring

end Places2

theorem red_eq_of_eq_zpow_mul {L : Type*} [Field L] {A' : ValuationSubring L} {k' : Type*} [Field k'] (red' : A' →+* k')
    (hker : ∀ c : A', red' c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A')
    (ϖ' : A') (hϖm : ϖ' ∈ IsLocalRing.maximalIdeal A') (hϖ0 : (ϖ' : L) ≠ 0)
    (u : A') (hu : red' u ≠ 0) (X : A') (hX : red' X ≠ 0) (t : ℤ)
    (h : (X : L) = (ϖ' : L) ^ t * (u : L)) : t = 0 ∧ red' X = red' u := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exfalso
    apply hu
    have h1 : (u : L) = (ϖ' : L) ^ (-t).toNat * (X : L) := by
      rw [h, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, one_mul]
    have hu' : u = ϖ' ^ (-t).toNat * X := Subtype.ext (by push_cast; exact h1)
    rw [hker, hu']
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))
  · refine ⟨rfl, ?_⟩
    congr 1
    exact Subtype.ext (by rw [h, zpow_zero, one_mul])
  · exfalso
    apply hX
    have hX' : X = ϖ' ^ t.toNat * u := Subtype.ext (by push_cast; rw [h, ← zpow_natCast, Int.toNat_of_nonneg ht.le])
    rw [hker, hX']
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))

theorem red_eq_red_of_eq_zpow_mul {L : Type*} [Field L] {A' : ValuationSubring L} {k' : Type*} [Field k'] (red' : A' →+* k')
    (hker : ∀ c : A', red' c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A')
    (ϖ' : A') (hϖm : ϖ' ∈ IsLocalRing.maximalIdeal A') (hϖ0 : (ϖ' : L) ≠ 0)
    (X₁ X₂ : A') (h₁ : red' X₁ ≠ 0) (h₂ : red' X₂ ≠ 0) (t : ℤ)
    (h : (X₁ : L) = (ϖ' : L) ^ t * (X₂ : L)) : red' X₁ = red' X₂ :=
  (red_eq_of_eq_zpow_mul red' hker ϖ' hϖm hϖ0 X₂ h₂ X₁ h₁ t h).2

section Dict

set_option maxHeartbeats 64000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve.UVCrossingModel Valued in

theorem exists_red_prod_evalAt_y_pow_ord_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (j : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
          𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    (βV : UVCrossingModel W (π ^ E)) (hβV : IsUnit βV) (hιy : ι (algebraMap ↥(R.nodeIntegersOver K w) _ c.y) = V (π ^ E) * βV)
    [IsAlgClosed k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hιord₁ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hιord₂ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (ρ : W →+* k) (hρ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ρ (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)) = NodeLocalized.redRestrict red K o)
    (Gβ : MvPowerSeries (Fin 2) W) (hGβ : mk (π ^ E) Gβ = βV)
    (g : ↥(R.nodeIntegersOver K w)) (hg : g ≠ 0)
    (abg : PowerSeries W × PowerSeries W) (hbg : PowerSeries.constantCoeff abg.2 = 0)
    (habg : mk (π ^ E) (inU abg.1 + inV abg.2) = ι (algebraMap ↥(R.nodeIntegersOver K w) _ g))
    (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hT : ∀ V, V ∈ T ↔ (V.ord ((g : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w)) :
    ((∑ V ∈ T, (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℤ) = endU E abg - endV E abg ∧
    ∃ (s : ℕ) (hmem : (∏ V ∈ T, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
          (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat) *
        (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)⁻¹ ∈ A),
      red ⟨_, hmem⟩ = normProdK ρ π E (ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)) *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ (endU E abg - endV E abg).toNat := by
  classical

  haveI hRdom : IsDomain (UVCrossingModel W (π ^ E)) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE).1
  haveI hRloc : IsLocalRing (UVCrossingModel W (π ^ E)) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE).2.1
  set jj : ↥(R.nodeIntegersOver K w) →+* UVCrossingModel W (π ^ E) := ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) with hjjdef
  have hjj : ∀ b : ↥(R.nodeIntegersOver K w), jj b = ι (algebraMap _ _ b) := fun b => rfl
  have hBinj : Function.Injective (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) := by
    haveI : IsHausdorff (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) :=
      IsHausdorff.of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    exact AdicCompletion.of_injective (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
  have hjinj : Function.Injective jj := ι.injective.comp hBinj
  have hG0 : ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ≠ 0 := fun h0 => hg (hjinj (by rw [hjj, h0, map_zero]))
  have hϖm : R.nodeConst K w ϖ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rw [hmax]; exact Ideal.subset_span (by simp)
  have hgF : ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hg (Subtype.ext h)
  have hRdim := ringKrullDim_le_two π hπ E hE

  have hmemV : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.reduceFst V = w →
      ∀ b : ↥(R.nodeIntegersOver K w), (b : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    fun V hV b => R.mem_toValuationSubring_of_mem_nodeIntegers b.2.1 hV
  obtain ⟨ker, hker⟩ : ∃ ker : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Ideal ↥(R.nodeIntegersOver K w),
      ∀ V, P.reduceFst V = w → ∀ b : ↥(R.nodeIntegersOver K w),
        b ∈ ker V ↔ V.evalAt ((b : ↥(modularFunctionFieldBar (N * q)))) = 0 := by
    refine ⟨fun V => if hV : P.reduceFst V = w then
      (IsLocalRing.maximalIdeal ↥V.toValuationSubring).comap
        ((R.nodeIntegersOver K w).subtype.codRestrict V.toValuationSubring.toSubring (fun b => hmemV V hV b))
      else ⊥, ?_⟩
    intro V hV b
    simp only [dif_pos hV, Ideal.mem_comap]
    rw [ValuationSubring.valuation_lt_one_iff, Ws12NodeTel.evalAt_eq_zero_iff V (hmemV V hV b)]
    rfl
  have hkerV : ∀ V ∈ T, P.reduceFst V = w ∧ (ker V).IsPrime ∧
      ker V ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) ∧
      (∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ ker V) ∧ g ∈ ker V ∧ ker V ≠ ⊥ := by
    intro V hV
    obtain ⟨hord, hVw⟩ := (hT V).mp hV
    obtain ⟨h1, h2, h3, h4⟩ :=
      R.ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem K w V hVw (ker V) (hker V hVw)
    exact ⟨hVw, h1, h2, h3, h4 g hord, fun h0 => hg (by have := h4 g hord; rw [h0] at this; exact (Ideal.mem_bot.mp this))⟩

  set 𝒬 : Finset (Ideal ↥(R.nodeIntegersOver K w)) := T.image ker with h𝒬def
  have h𝒬 : ∀ 𝔮 ∈ 𝒬, 𝔮.IsPrime ∧ 𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) ∧
      (∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮) ∧ g ∈ 𝔮 ∧ 𝔮 ≠ ⊥ ∧
      (∀ V, V ∈ T.filter (fun V => ker V = 𝔮) ↔ (P.reduceFst V = w ∧
        ∀ b : ↥(R.nodeIntegersOver K w), b ∈ 𝔮 ↔ V.evalAt ((b : ↥(modularFunctionFieldBar (N * q)))) = 0)) := by
    intro 𝔮 h𝔮
    obtain ⟨V₀, hV₀, rfl⟩ := Finset.mem_image.mp h𝔮
    obtain ⟨hV₀w, hpr, hne, hcst, hgq, hq0⟩ := hkerV V₀ hV₀
    refine ⟨hpr, hne, hcst, hgq, hq0, fun V => ?_⟩
    rw [Finset.mem_filter, hT V]
    constructor
    · rintro ⟨⟨-, hVw⟩, hkq⟩
      exact ⟨hVw, fun b => by rw [← hkq]; exact hker V hVw b⟩
    · rintro ⟨hVw, hq⟩
      have hkq : ker V = ker V₀ := by
        ext b; rw [hker V hVw b, hq b]
      refine ⟨⟨?_, hVw⟩, hkq⟩
      intro hord
      have hev : V.evalAt ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 0 := (hq g).mp hgq
      exact (V.evalAt_ne_zero (Ws12NodeTel.isRational_of_place V) hgF hord) hev

  have hTfib : ∀ V ∈ T, ker V ∈ 𝒬 := fun V hV => Finset.mem_image_of_mem ker hV

  have hper : ∀ 𝔮 (h𝔮 : 𝔮 ∈ 𝒬), haveI : 𝔮.IsPrime := (h𝒬 𝔮 h𝔮).1; ∃ (n : PrimeSpectrum (UVCrossingModel W (π ^ E)) → ℕ)
      (u : PrimeSpectrum (UVCrossingModel W (π ^ E)) → Wˣ),
      ((T.filter (fun V => ker V = 𝔮)).card : ℕ∞) = ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal),
          (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) ∧
      (∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
        Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes → const (π ^ E) π ∉ Q.asIdeal →
          Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (ι (algebraMap ↥(R.nodeIntegersOver K w) _ c.y))) = π ^ n Q * (u Q : W)) ∧
      ((∏ V ∈ T.filter (fun V => ker V = 𝔮), V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) : AlgebraicClosure ℚ) :
          (A.valuation).Completion) =
        ((j (τ.symm (π ^ (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
              (_ : Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), n Q) *
            ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
              (_ : Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), (u Q : W))) :
              𝒪[(A.valuation).Completion]) : (A.valuation).Completion) ∧
      (∀ V ∈ T.filter (fun V => ker V = 𝔮),
        ((V.ord ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))).toNat : ℕ∞) =
          Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g}))) ∧
      (∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
        Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes → const (π ^ E) π ∉ Q.asIdeal →
          Module.length (Localization.AtPrime Q.asIdeal)
              (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)})) =
            Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g}))) := by
    intro 𝔮 h𝔮
    obtain ⟨hpr, hne, hcst, hgq, hq0, hfib⟩ := h𝒬 𝔮 h𝔮
    haveI := hpr
    have hcard := R.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ
      αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 hcst hq0 hqN hO hιord₁ hιord₂ _ hfib
    obtain ⟨n, u, hnu, hprod⟩ := R.exists_prod_evalAt_y_eq_pow_mul_prod_units_of_forall_iff_evalAt_eq_zero K w c ϖ hϖ0 hmax hres
      hVI hwss π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 hcst hq0 j hj βV hβV hιy _ hfib hcard
    refine ⟨n, u, hcard, hnu, hprod, fun V hV => ?_, fun Q hQ hQπ => ?_⟩
    · exact R.toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero K w hfrac V
        ((hfib V).mp hV).1 𝔮 ((hfib V).mp hV).2 (fun 𝔭 h𝔭 hlt => hht 𝔭 𝔮 h𝔭 inferInstance hne hlt) g hg
    · exact R.length_localizedModule_quotient_map_eq_of_mem_minimalPrimes K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ
        αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 hcst hq0 hqN hO hιord₁ hιord₂ Q hQ hQπ g hg

  have hcover : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)), Q.asIdeal ≠ ⊥ → const (π ^ E) π ∉ Q.asIdeal →
      ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ∈ Q.asIdeal →
      Q.asIdeal.comap jj ∈ 𝒬 ∧ Q.asIdeal ∈ (Ideal.map jj (Q.asIdeal.comap jj)).minimalPrimes := by
    intro Q hQ0 hQπ hGQ
    set 𝔮' : Ideal ↥(R.nodeIntegersOver K w) := Q.asIdeal.comap jj with h𝔮'def
    haveI h𝔮'pr : 𝔮'.IsPrime := Ideal.IsPrime.comap jj
    have hg𝔮' : g ∈ 𝔮' := by show jj g ∈ Q.asIdeal; rw [hjj]; exact hGQ
    have h𝔮'0 : 𝔮' ≠ ⊥ := fun h0 => hg (by rw [h0] at hg𝔮'; exact Ideal.mem_bot.mp hg𝔮')

    have hcst' : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮' := by
      intro o ho hmem
      have hmem' : const (π ^ E) (τ (algebraMap _ _ o)) ∈ Q.asIdeal := by
        have : jj (R.nodeConst K w o) ∈ Q.asIdeal := hmem
        rwa [hjj, hτ] at this
      have hto0 : τ (algebraMap _ _ o) ≠ 0 := by
        intro h0
        apply ho
        haveI : IsHausdorff (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) :=
          IsHausdorff.of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        have hOinj : Function.Injective (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K))) :=
          AdicCompletion.of_injective (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) _
        exact hOinj (τ.injective (by rw [h0, map_zero, map_zero]))

      obtain ⟨n, v, hvunit, hnv⟩ : ∃ (n : ℕ) (v : W), IsUnit v ∧ τ (algebraMap _ _ o) = π ^ n * v := by
        obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hto0 hπ
        exact ⟨n, v, v.isUnit, by rw [hv]; ring⟩
      rw [hnv, ← constHom_apply, map_mul, map_pow, constHom_apply, constHom_apply] at hmem'
      rcases Q.isPrime.mem_or_mem hmem' with h | h
      · exact hQπ (Q.isPrime.mem_of_pow_mem _ h)
      · exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
          (by obtain ⟨z, hz⟩ := (hvunit.map (constHom (π ^ E))).exists_right_inv
              rw [constHom_apply] at hz
              rw [← hz]; exact Ideal.mul_mem_right _ _ h))
    have hne' : 𝔮' ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := fun h => hcst' ϖ hϖ0 (h ▸ hϖm)

    have hπm : const (π ^ E) π ∈ IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ E)) := by
      apply (IsLocalRing.mem_maximalIdeal _).mpr
      intro hu
      rw [← hιϖ] at hu
      have hu' : IsUnit (algebraMap ↥(R.nodeIntegersOver K w)
          (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) (R.nodeConst K w ϖ)) := by
        have := hu.map ι.symm
        rwa [RingEquiv.symm_apply_apply] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp hϖm (AdicCompletion.isUnit_of_isUnit_algebraMap hu')
    have hQm : Q.asIdeal ≠ IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ E)) := fun h => hQπ (h ▸ hπm)
    have hmapne : Ideal.map jj 𝔮' ≠ ⊥ := by
      intro h0
      have : jj g ∈ Ideal.map jj 𝔮' := Ideal.mem_map_of_mem jj hg𝔮'
      rw [h0, Ideal.mem_bot, hjj] at this
      exact hG0 this
    have hmin : Q.asIdeal ∈ (Ideal.map jj 𝔮').minimalPrimes :=
      Ws12NodeTel.mem_minimalPrimes_of_ne_bot hRdim _ hmapne Q.asIdeal Ideal.map_comap_le hQm
    refine ⟨?_, hmin⟩

    have hfib' : ∀ V, V ∈ T.filter (fun V => ker V = 𝔮') ↔ (P.reduceFst V = w ∧
        ∀ b : ↥(R.nodeIntegersOver K w), b ∈ 𝔮' ↔ V.evalAt ((b : ↥(modularFunctionFieldBar (N * q)))) = 0) := by
      intro V
      rw [Finset.mem_filter, hT V]
      constructor
      · rintro ⟨⟨-, hVw⟩, hkq⟩
        exact ⟨hVw, fun b => by rw [← hkq]; exact hker V hVw b⟩
      · rintro ⟨hVw, hq⟩
        have hkq : ker V = 𝔮' := by ext b; rw [hker V hVw b, hq b]
        refine ⟨⟨?_, hVw⟩, hkq⟩
        intro hord
        exact (V.evalAt_ne_zero (Ws12NodeTel.isRational_of_place V) hgF hord) ((hq g).mp hg𝔮')
    have hcard' := R.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ
      αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮' hcst' h𝔮'0 hqN hO hιord₁ hιord₂ _ hfib'
    have hrk := (exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem π hπ E hE Q hQ0 hQπ).1

    have hfinBr : {Q' : PrimeSpectrum (UVCrossingModel W (π ^ E)) |
        Q'.asIdeal ∈ (Ideal.map jj 𝔮').minimalPrimes ∧ const (π ^ E) π ∉ Q'.asIdeal}.Finite := by
      refine (setOf_horizontal_mem_finite π hπ E hE _ hG0).subset ?_
      rintro Q' ⟨hQ'min, hQ'π⟩
      obtain ⟨h0, -, hG⟩ := (show Q'.asIdeal ≠ ⊥ ∧ Q'.asIdeal.comap jj = 𝔮' ∧ ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ∈ Q'.asIdeal from by
        obtain ⟨h0, hc⟩ := Ws12NodeTel.ne_bot_and_comap_eq_of_map_le jj hjinj hht 𝔮' g hg hg𝔮' Q'.asIdeal hQ'min.1.2
          ⟨R.nodeConst K w ϖ, hϖm, fun h => hQ'π (by rw [hjj, hιϖ] at h; exact h)⟩
        exact ⟨h0, hc, hQ'min.1.2 (Ideal.mem_map_of_mem jj hg𝔮')⟩)
      exact ⟨h0, hQ'π, hG⟩
    have hsum : (∑ᶠ (Q' : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q'.asIdeal ∈ (Ideal.map jj 𝔮').minimalPrimes ∧ const (π ^ E) π ∉ Q'.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q'.asIdeal) : ℕ∞)) =
        ∑ Q' ∈ hfinBr.toFinset, (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q'.asIdeal) : ℕ∞) := by
      rw [finsum_eq_sum_of_support_subset (s := hfinBr.toFinset) _ ?_]
      · refine Finset.sum_congr rfl fun Q' hQ' => ?_
        rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hQ'
        rw [finsum_eq_if, if_pos hQ']
      · intro Q' hQ'
        rw [Function.mem_support] at hQ'
        by_contra hQH
        apply hQ'
        rw [finsum_eq_if]
        split_ifs with h
        · exact absurd ((Set.Finite.mem_toFinset hfinBr).mpr h) hQH
        · rfl
    have hQmem : Q ∈ hfinBr.toFinset := by rw [Set.Finite.mem_toFinset]; exact ⟨hmin, hQπ⟩
    have hge : (1 : ℕ∞) ≤ ((T.filter (fun V => ker V = 𝔮')).card : ℕ∞) := by
      rw [hcard', hsum]
      calc (1 : ℕ∞) ≤ (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) := by exact_mod_cast hrk
        _ ≤ _ := Finset.single_le_sum (f := fun Q' : PrimeSpectrum (UVCrossingModel W (π ^ E)) =>
              (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q'.asIdeal) : ℕ∞)) (fun _ _ => bot_le) hQmem
    obtain ⟨V₁, hV₁⟩ : (T.filter (fun V => ker V = 𝔮')).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℕ∞) < ((T.filter (fun V => ker V = 𝔮')).card : ℕ∞) := lt_of_lt_of_le zero_lt_one hge
      exact_mod_cast this
    rw [Finset.mem_filter] at hV₁
    rw [← hV₁.2]
    exact Finset.mem_image_of_mem ker hV₁.1

  have hcontr : ∀ 𝔮 ∈ 𝒬, ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes → const (π ^ E) π ∉ Q.asIdeal →
      Q.asIdeal ≠ ⊥ ∧ Q.asIdeal.comap jj = 𝔮 ∧ ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ∈ Q.asIdeal := by
    intro 𝔮 h𝔮 Q hQ hQπ
    obtain ⟨hpr, hne, hcst, hgq, hq0, -⟩ := h𝒬 𝔮 h𝔮
    haveI := hpr
    obtain ⟨h0, hc⟩ := Ws12NodeTel.ne_bot_and_comap_eq_of_map_le jj hjinj hht 𝔮 g hg hgq Q.asIdeal hQ.1.2
      ⟨R.nodeConst K w ϖ, hϖm, fun h => hQπ (by rw [hjj, hιϖ] at h; exact h)⟩
    exact ⟨h0, hc, hQ.1.2 (Ideal.mem_map_of_mem jj hgq)⟩

  have hfinH : {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) |
      Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ∈ Q.asIdeal}.Finite :=
    setOf_horizontal_mem_finite π hπ E hE _ hG0
  set H := hfinH.toFinset with hHdef
  have hmemH : ∀ Q, Q ∈ H ↔ (Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ∈ Q.asIdeal) :=
    fun Q => by rw [hHdef, Set.Finite.mem_toFinset]; rfl
  have hHmaps : ∀ Q ∈ H, Q.asIdeal.comap jj ∈ 𝒬 := fun Q hQ => by
    obtain ⟨h0, hπ', hG⟩ := (hmemH Q).mp hQ
    exact (hcover Q h0 hπ' hG).1

  have hBr : ∀ 𝔮 ∈ 𝒬, ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      (Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal) ↔ (Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮)) := by
    intro 𝔮 h𝔮 Q
    rw [Finset.mem_filter, hmemH]
    constructor
    · rintro ⟨hmin, hQπ⟩
      obtain ⟨h0, hc, hG⟩ := hcontr 𝔮 h𝔮 Q hmin hQπ
      exact ⟨⟨h0, hQπ, hG⟩, hc⟩
    · rintro ⟨⟨h0, hQπ, hG⟩, hc⟩
      refine ⟨?_, hQπ⟩
      rw [← hc]
      exact (hcover Q h0 hQπ hG).2

  have hfinsumBr : ∀ 𝔮 ∈ 𝒬, ∀ (F : PrimeSpectrum (UVCrossingModel W (π ^ E)) → ℕ∞),
      (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), F Q) =
        ∑ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), F Q := by
    intro 𝔮 h𝔮 F
    rw [finsum_eq_sum_of_support_subset (s := H.filter (fun Q => Q.asIdeal.comap jj = 𝔮)) _ ?_]
    · refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [finsum_eq_if, if_pos ((hBr 𝔮 h𝔮 Q).mpr hQ)]
    · intro Q hQ
      rw [Function.mem_support] at hQ
      by_contra hQH
      apply hQ
      rw [finsum_eq_if, if_neg (fun h => hQH ((hBr 𝔮 h𝔮 Q).mp h))]
  have hfinprodBr : ∀ 𝔮 ∈ 𝒬, ∀ (F : PrimeSpectrum (UVCrossingModel W (π ^ E)) → W),
      (∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), F Q) =
        ∏ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), F Q := by
    intro 𝔮 h𝔮 F
    rw [finprod_eq_prod_of_mulSupport_subset (s := H.filter (fun Q => Q.asIdeal.comap jj = 𝔮)) _ ?_]
    · refine Finset.prod_congr rfl fun Q hQ => ?_
      rw [finprod_eq_if, if_pos ((hBr 𝔮 h𝔮 Q).mpr hQ)]
    · intro Q hQ
      rw [Function.mem_mulSupport] at hQ
      by_contra hQH
      apply hQ
      rw [finprod_eq_if, if_neg (fun h => hQH ((hBr 𝔮 h𝔮 Q).mp h))]

  choose! nq uq hcardq hnuq hprodq hℓq hLBq using hper

  obtain ⟨ℓB, hℓB⟩ : ∃ ℓB : Ideal ↥(R.nodeIntegersOver K w) → ℕ, ∀ (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime],
      ℓB 𝔮 = (Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g}))).toNat := by
    classical
    refine ⟨fun 𝔮 => if h : 𝔮.IsPrime then (by haveI := h; exact
      (Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g}))).toNat) else 0,
      fun 𝔮 h => ?_⟩
    simp only [dif_pos h]
  obtain ⟨hnn, hfs⟩ := Ws12NodeTel.endU_sub_endV_eq_finsum π hπ E hE _ hG0 abg hbg habg

  have hmodel : (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
      (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)}))) =
      ∑ Q ∈ H, (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)})) := by
    rw [finsum_eq_sum_of_support_subset (s := H) _ ?_]
    · refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [finsum_eq_if, if_pos ⟨((hmemH Q).mp hQ).1, ((hmemH Q).mp hQ).2.1⟩]
    · intro Q hQ
      rw [Function.mem_support] at hQ
      by_contra hQH
      apply hQ
      rw [finsum_eq_if]
      by_cases hp : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal
      · have hGQ : ι (algebraMap ↥(R.nodeIntegersOver K w) _ g) ∉ Q.asIdeal := fun h => hQH ((hmemH Q).mpr ⟨hp.1, hp.2, h⟩)
        haveI := Q.isPrime
        rw [if_pos hp, Ws12NodeTel.length_localizedModule_quotient_eq_zero _ Q.asIdeal hGQ, mul_zero]
      · rw [if_neg hp]

  have hplace : ((∑ V ∈ T, (V.ord ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))).toNat : ℕ) : ℕ∞) =
      ∑ Q ∈ H, (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)})) := by
    rw [Nat.cast_sum, ← Finset.sum_fiberwise_of_maps_to hTfib]
    rw [← Finset.sum_fiberwise_of_maps_to hHmaps]
    refine Finset.sum_congr rfl fun 𝔮 h𝔮 => ?_
    haveI : 𝔮.IsPrime := (h𝒬 𝔮 h𝔮).1

    have h1 : (∑ V ∈ T.filter (fun V => ker V = 𝔮), ((V.ord ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))).toNat : ℕ∞)) =
        ((T.filter (fun V => ker V = 𝔮)).card : ℕ∞) *
          Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g})) := by
      rw [Finset.sum_congr rfl (fun V hV => hℓq 𝔮 h𝔮 V hV), Finset.sum_const, nsmul_eq_mul]
    rw [h1, hcardq 𝔮 h𝔮, hfinsumBr 𝔮 h𝔮, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    obtain ⟨hmin, hQπ⟩ := (hBr 𝔮 h𝔮 Q).mpr hQ
    rw [hLBq 𝔮 h𝔮 Q hmin hQπ]
  have hcount : ((∑ V ∈ T, (V.ord ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))).toNat : ℕ) : ℤ) =
      endU E abg - endV E abg := by
    have hℕ : (∑ V ∈ T, (V.ord ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))).toNat) = (endU E abg - endV E abg).toNat := by
      have := hplace.trans (hmodel.symm.trans hfs.symm)
      exact_mod_cast this
    rw [hℕ, Int.toNat_of_nonneg hnn]
  refine ⟨hcount, ?_⟩

  set s : ℕ := ∑ 𝔮 ∈ 𝒬, (∑ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), nq 𝔮 Q) *
      ℓB 𝔮 with hsdef
  set 𝕌 : W := ∏ 𝔮 ∈ 𝒬, (∏ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), (uq 𝔮 Q : W)) ^
      ℓB 𝔮 with h𝕌def
  have h𝕌unit : IsUnit 𝕌 := by
    rw [h𝕌def]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun 𝔮 _ => IsUnit.pow _ ?_)
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun Q _ => Units.isUnit _)

  have hordq : ∀ 𝔮 ∈ 𝒬, ∀ V ∈ T.filter (fun V => ker V = 𝔮),
      (V.ord ((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))).toNat =
        ℓB 𝔮 := by
    intro 𝔮 h𝔮 V hV
    haveI : 𝔮.IsPrime := (h𝒬 𝔮 h𝔮).1
    have h := hℓq 𝔮 h𝔮 V hV
    rw [hℓB 𝔮, ← h, ENat.toNat_coe]

  have hfinsumBrN : ∀ 𝔮 ∈ 𝒬, ∀ (F : PrimeSpectrum (UVCrossingModel W (π ^ E)) → ℕ),
      (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map jj 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal), F Q) =
        ∑ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), F Q := by
    intro 𝔮 h𝔮 F
    rw [finsum_eq_sum_of_support_subset (s := H.filter (fun Q => Q.asIdeal.comap jj = 𝔮)) _ ?_]
    · refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [finsum_eq_if, if_pos ((hBr 𝔮 h𝔮 Q).mpr hQ)]
    · intro Q hQ
      rw [Function.mem_support] at hQ
      by_contra hQH
      apply hQ
      rw [finsum_eq_if, if_neg (fun h => hQH ((hBr 𝔮 h𝔮 Q).mp h))]
  set θC : AlgebraicClosure ℚ →+* (A.valuation).Completion :=
    (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* (A.valuation).Completion).comp
      (WithVal.equiv A.valuation).symm.toRingHom with hθCdef
  have hθ : ∀ x : AlgebraicClosure ℚ, ((x : AlgebraicClosure ℚ) : (A.valuation).Completion) = θC x := fun _ => rfl
  have hprodC : ((∏ V ∈ T, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
        (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat : AlgebraicClosure ℚ) : (A.valuation).Completion) =
      ((j (τ.symm (π ^ s * 𝕌)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
    have hfibre : ∀ 𝔮 ∈ 𝒬, (∏ V ∈ T.filter (fun V => ker V = 𝔮), V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
        (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat) =
        (∏ V ∈ T.filter (fun V => ker V = 𝔮), V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q))))) ^ ℓB 𝔮 := by
      intro 𝔮 h𝔮
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun V hV => by rw [hordq 𝔮 h𝔮 V hV]
    show θC _ = _
    rw [← Finset.prod_fiberwise_of_maps_to hTfib, Finset.prod_congr rfl hfibre]

    have hW : (∏ 𝔮 ∈ 𝒬, (π ^ (∑ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), nq 𝔮 Q) *
        ∏ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), (uq 𝔮 Q : W)) ^ ℓB 𝔮) = π ^ s * 𝕌 := by
      rw [hsdef, h𝕌def]
      simp only [mul_pow, ← pow_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← hW, map_prod, map_prod, map_prod]
    push_cast
    refine Finset.prod_congr rfl fun 𝔮 h𝔮 => ?_
    rw [map_pow, map_pow, map_pow]
    push_cast
    have hq' := hprodq 𝔮 h𝔮
    rw [hfinsumBrN 𝔮 h𝔮, hfinprodBr 𝔮 h𝔮] at hq'
    exact congrArg (fun t : (A.valuation).Completion => t ^ ℓB 𝔮) hq'

  have hjπ : ((j (τ.symm π) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
      (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) : (A.valuation).Completion) := by
    rw [← hτϖ, RingEquiv.symm_apply_apply]; exact hj ϖ
  obtain ⟨hmem, hred⟩ : ∃ hmem : (∏ V ∈ T, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
        (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat) *
        (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)⁻¹ ∈ A, red ⟨_, hmem⟩ = ρ 𝕌 := by
    have hϖL0 : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
    have hker' : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := Ws12NodeTel.red_eq_zero_iff R
    have hredϖ' : red ⟨((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := by
      rw [hker', IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Ws12NodeTel.isUnit_coeffSubring_iff, ← mem_nonunits_iff,
        ← IsLocalRing.mem_maximalIdeal, hϖgen]
      exact Ideal.mem_span_singleton_self ϖ
    have hρ' : ∀ o : ↥(NodeLocalized.coeffSubring A K), ρ (τ (algebraMap _ _ o)) = red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩ := hρ

    have hϖC0 : (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) : (A.valuation).Completion) ≠ 0 := by
      intro h
      have hv := Valued.valuedCompletion_apply (K := WithVal A.valuation) ((WithVal.equiv A.valuation).symm ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ))
      rw [h, map_zero] at hv
      exact ((Valuation.ne_zero_iff A.valuation).mpr hϖL0) hv.symm
    have hz : (((∏ V ∈ T, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
          (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat) *
          (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)⁻¹ : AlgebraicClosure ℚ) : (A.valuation).Completion) =
        ((j (τ.symm 𝕌) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
      show θC _ = _
      have hϖC0' : θC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := hϖC0
      have hjπ' : ((j (τ.symm π) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          θC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := hjπ
      have hP : θC (∏ V ∈ T, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
          (V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat) =
          θC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s *
            ((j (τ.symm 𝕌) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
        have h := hprodC
        rw [map_mul, map_pow, map_mul, map_pow] at h
        push_cast at h
        rw [hjπ'] at h
        exact h
      apply mul_right_cancel₀ (pow_ne_zero s hϖC0')
      rw [← map_pow, ← map_mul, inv_mul_cancel_right₀ (pow_ne_zero s hϖL0), hP, mul_comm, map_pow]
    exact Ws12NodeTel.exists_mem_and_red_eq_of_coe_eq_coe_adicCompletion A red hker' (NodeLocalized.coeffSubring A K)
      inf_le_left ϖ hϖgen hϖL0 hredϖ' τ ρ hρ' j hj 𝕌 _ hz
  refine ⟨s, hmem, ?_⟩
  rw [hred]

  have hρπ0 : ρ π = 0 := by
    have hredϖ' : red ⟨((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := by
      rw [Ws12NodeTel.red_eq_zero_iff R, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Ws12NodeTel.isUnit_coeffSubring_iff,
        ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖgen]
      exact Ideal.mem_span_singleton_self ϖ
    rw [← hτϖ, hρ ϖ]
    exact hredϖ'
  have hkerρ : ∀ a ∈ IsLocalRing.maximalIdeal W, ρ a = 0 := by
    intro a ha
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hρπ0, zero_mul]
  haveI hρloc : IsLocalHom ρ := ⟨fun a ha => by
    by_contra hna
    exact ha.ne_zero (hkerρ a ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna)))⟩
  have hρu : ∀ 𝔮 ∈ 𝒬, ∀ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮),
      ρ (uq 𝔮 Q : W) = ρ (unitPart π (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (π ^ E))))) *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    intro 𝔮 h𝔮 Q hQ
    obtain ⟨hmin, hQπ⟩ := (hBr 𝔮 h𝔮 Q).mpr hQ
    have hQH := (Finset.mem_filter.mp hQ).1
    obtain ⟨hQ0, -, -⟩ := (hmemH Q).mp hQH
    haveI := Q.isPrime
    obtain ⟨hFree, hFin⟩ := free_and_finite_quotient_of_ne_bot_of_const_notMem π hπ E hE Q.asIdeal hQ0 hQπ
    have hnu := hnuq 𝔮 h𝔮 Q hmin hQπ
    rw [hιy, map_mul, map_mul] at hnu
    have hβn : IsUnit (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal βV)) := (hβV.map _).map _
    have hVn0 : Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (π ^ E))) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hnu
      exact (mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (Units.ne_zero _)) hnu.symm
    have hu : (uq 𝔮 Q : W) = unitPart π (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (π ^ E))) *
        Algebra.norm W (Ideal.Quotient.mk Q.asIdeal βV)) :=
      (Ws12NodeTel.unitPart_eq_of_eq_pow_mul π hπ _ (nq 𝔮 Q) _ (Units.isUnit _) hnu).symm
    rw [hu, Ws12NodeTel.unitPart_mul_of_isUnit π hπ _ _ hVn0 hβn, map_mul]
    congr 1
    have h2 := residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank π hπ E hE Q.asIdeal Gβ
    rw [hGβ] at h2
    have h3 := congrArg (IsLocalRing.ResidueField.lift ρ) h2
    rw [IsLocalRing.ResidueField.lift_residue_apply] at h3
    rw [h3, map_pow, IsLocalRing.ResidueField.lift_residue_apply]

  have hℓfin : ∀ Q ∈ H, Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)})) ≠ ⊤ := by
    intro Q hQ htop
    have h := hfs.trans hmodel
    have hle := Finset.single_le_sum (f := fun Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) =>
      (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)})))
      (fun _ _ => bot_le) hQ
    rw [← h] at hle
    obtain ⟨hQ0, hQπ, -⟩ := (hmemH Q).mp hQ
    have hrk := (exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem π hπ E hE Q hQ0 hQπ).1
    have hrk0 : (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hrk)
    simp only [htop, ENat.mul_top hrk0, top_le_iff] at hle
    exact ENat.coe_ne_top _ hle
  have hexp : (∑ Q ∈ H, Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) *
      (Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)}))).toNat) =
      (endU E abg - endV E abg).toNat := by
    have h := hfs.trans hmodel
    rw [Finset.sum_congr rfl (fun Q hQ => by rw [← ENat.coe_toNat (hℓfin Q hQ)])] at h
    push_cast at h ⊢
    exact_mod_cast h.symm

  have hnP : normProdK ρ π E (ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)) =
      ∏ Q ∈ H, ρ (unitPart π (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (π ^ E))))) ^
        (Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)}))).toNat := by
    unfold normProdK
    rw [finprod_eq_prod_of_mulSupport_subset (s := H) _ ?_]
    · refine Finset.prod_congr rfl fun Q hQ => ?_
      rw [finprod_eq_if, if_pos ((hmemH Q).mp hQ)]
    · intro Q hQ
      rw [Function.mem_mulSupport] at hQ
      by_contra hQH
      apply hQ
      rw [finprod_eq_if, if_neg (fun h => hQH ((hmemH Q).mpr h))]

  rw [h𝕌def, map_prod]
  have hterm : ∀ 𝔮 ∈ 𝒬, ρ ((∏ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮), (uq 𝔮 Q : W)) ^
      ℓB 𝔮) =
      ∏ Q ∈ H.filter (fun Q => Q.asIdeal.comap jj = 𝔮),
        (ρ (unitPart π (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (π ^ E))))) ^
          (Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)}))).toNat *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) *
          (Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)}))).toNat)) := by
    intro 𝔮 h𝔮
    haveI : 𝔮.IsPrime := (h𝒬 𝔮 h𝔮).1
    rw [map_pow, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun Q hQ => ?_
    obtain ⟨hmin, hQπ⟩ := (hBr 𝔮 h𝔮 Q).mpr hQ
    rw [hρu 𝔮 h𝔮 Q hQ, hℓB 𝔮, ← hLBq 𝔮 h𝔮 Q hmin hQπ, mul_pow, ← pow_mul]
  rw [Finset.prod_congr rfl hterm, Finset.prod_fiberwise_of_maps_to hHmaps, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hnP, hexp]

end Dict

end Ws12NodeTel

open Ws12NodeTel

set_option maxHeartbeats 64000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)

    (K K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKK' : K ≤ K') [FiniteDimensional ℚ K']
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) (hwφ : arithFrobC q k N • w ∈ W₀) (hVI : R.ValueIntegralityLaw w)
    (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)

    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K')) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ ^ eK * ε)

    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K' w)) (hu : IsUnit u)
    (hxy : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y = (R.nodeConst K' w ϖ : ↥(modularFunctionFieldBar (N * q))) ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    [IsLocalRing ↥(R.nodeIntegersOver K' w)] [IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (hmax' : maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    (hbr : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y}).IsPrime ∧
        Subring.inclusion hBB' c.y ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x} ∧ Subring.inclusion hBB' c.x ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o))

    (depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℚ)
    (hdepthQ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
        0 < depthQ V ∧ c.yDepth V ^ (depthQ V).den = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (depthQ V).num.toNat)

    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K')
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (hc₁ : c₁ ∈ K') (hc₂ : c₂ ∈ K') (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)

    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f)

    (hstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ D.support, P.reduceFst V = w →
      D (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = D V)

    (m : ℤ) (hm : (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ) * depthQ V) = m)
    (hN : (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V) =
      w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩))
    (m₁ m₂ : ℤ) (η₁ η₂ : ↥(NodeLocalized.coeffSubring A K')) (hη₁ : IsUnit η₁) (hη₂ : IsUnit η₂)
    (hc₁η : c₁ = ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₁ *
      ((η₁ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))
    (hc₂η : c₂ = ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₂ *
      ((η₂ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))
    (ηbar₁ ηbar₂ εbar u0 : kˣ)
    (hηbar₁ : NodeLocalized.redRestrict red K' η₁ = (ηbar₁ : k))
    (hηbar₂ : NodeLocalized.redRestrict red K' η₂ = (ηbar₂ : k))
    (hεbar : NodeLocalized.redRestrict red K' ε = (εbar : k))
    (hu0 : w.HasValue ((R.nodeResidue₁ w ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩ :
      ↥(modularFunctionFieldC k N)) : ↥(modularFunctionFieldC k N)) (u0 : k))
    (Θ : kˣ)
    (hΘ : ∃ hmem : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^ (-(D V))) *
        ((q : ℕ) : AlgebraicClosure ℚ) ^ m ∈ A, red ⟨_, hmem⟩ = (Θ : k)) :
    ∃ α₁ α₂ : kˣ,
      w.HasValue
        ((R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ^
            (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)))
        (α₁ : k) ∧
      (arithFrobC q k N • w).HasValue
        ((R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ^
            ((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)))
        (α₂ : k) ∧
      α₁ / α₂ =
        (ηbar₁ / ηbar₂) *
        (-1 : kˣ) ^ (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V) *
        u0 ^ ((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) *
        εbar ^ (-m) * Θ := by
  classical

  have hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A := Ws12NodeTel.red_eq_zero_iff R
  haveI hdvr0 : IsDiscreteValuationRing ↥(coeffSubring A K') := isDiscreteValuationRing_coeffSubring red hker K'
  have hϖirr : Irreducible ϖ := Ws12NodeTel.irreducible_of_redRestrict R K' ϖ hϖ
  obtain ⟨hWdom, hWdvr, hWcpl, hπ⟩ := PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖirr
  set π : (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) :=
    Ideal.Quotient.mk _ (PowerSeries.C ϖ) with hπdef
  set E : ℕ := ew * eK with hEdef
  have hE : 1 ≤ E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set c' : R.NodeCoordinates K' w := Ws12NodeTel.enlargeCoordinates R hBB' c with hc'
  have hxy' : c'.x * c'.y = R.nodeConst K' w ϖ ^ E * u := Subtype.ext hxy
  have hwss : w ∈ ssPlaces q N k := hW₀ w hw

  obtain ⟨θW, θ, hθWo, hθWX, hθsurj, hθC, hθ0, hθ1⟩ :=
    exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver R K' w c' ϖ hϖ hmax' hres
  have hdim := two_le_ringKrullDim_adicCompletion_nodeIntegersOver R K' w c' ϖ hbr.1 hbr.2.2.1
  have hθπ : θ (MvPowerSeries.C π) = algebraMap _ _ (R.nodeConst K' w ϖ) := by
    rw [show θ (MvPowerSeries.C π) = (θ.comp MvPowerSeries.C) π from rfl, hθC]; exact hθWo ϖ
  obtain ⟨ι, αU, βV, hαU, hβV, hιconst, hιx, hιy, hιord₁, hιord₂⟩ :=
    exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal R hqN hmodel W₀ hW₀ hreg hval
      K' w hw c' ϖ hϖ E hE u hu hxy' hmax π hπ θ hθsurj hθπ hθ0 hθ1 hdim
  have hιϖ : ι (algebraMap _ _ (R.nodeConst K' w ϖ)) = const (π ^ E) π := by rw [← hθπ]; exact hιconst π
  have hιo : ∀ o : ↥(coeffSubring A K'),
      ι (algebraMap _ _ (R.nodeConst K' w o)) = const (π ^ E) (Ideal.Quotient.mk _ (PowerSeries.C o)) := by
    intro o
    rw [← hθWo o, ← hθC]
    exact hιconst _

  haveI hWcplπ : IsAdicComplete (Ideal.span {π}) (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) := by
    rw [← hπ.maximalIdeal_eq]; exact hWcpl

  have hϖgen : maximalIdeal ↥(coeffSubring A K') = Ideal.span {ϖ} :=
    maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const R K' w ϖ π hπ E hE ι hιϖ
  obtain ⟨τ, hτ, hτϖ⟩ :=
    exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const R K' w ϖ hϖgen hres π hπ E hE ι hιϖ

  obtain ⟨ρ, hρw, hρτ, hρloc⟩ : ∃ ρ : (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) →+* k,
      (∀ o : ↥(coeffSubring A K'), ρ (Ideal.Quotient.mk _ (PowerSeries.C o)) = redRestrict red K' o) ∧
      (∀ o : ↥(coeffSubring A K'), ρ (τ (algebraMap _ _ o)) = redRestrict red K' o) ∧
      IsLocalHom ρ := by
    have hτw : ∀ o : ↥(coeffSubring A K'), τ (algebraMap _ _ o) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C o) := by
      intro o
      have h := (hτ o).symm.trans (hιo o)
      have h' : const (π ^ E) (τ (algebraMap _ _ o) -
          Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C o)) = 0 := by
        rw [← constHom_apply, map_sub, constHom_apply, constHom_apply, h, sub_self]
      exact sub_eq_zero.mp (Ws12NodeTel.const_eq_zero_imp π hπ E hE _ h')
    have hredϖ : redRestrict red K' ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
    have hkerI : ∀ a ∈ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ},
        ((redRestrict red K').comp (PowerSeries.constantCoeff : PowerSeries ↥(coeffSubring A K') →+* ↥(coeffSubring A K'))) a = 0 := by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, RingHom.comp_apply, map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub,
        map_neg, hredϖ, neg_zero, zero_mul]
    set ρ₀ := Ideal.Quotient.lift (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ})
      ((redRestrict red K').comp (PowerSeries.constantCoeff : PowerSeries ↥(coeffSubring A K') →+* ↥(coeffSubring A K'))) hkerI with hρ₀
    have hρ₀C : ∀ o : ↥(coeffSubring A K'),
        ρ₀ (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C o)) =
          redRestrict red K' o := by
      intro o
      rw [hρ₀, Ideal.Quotient.lift_mk, RingHom.comp_apply, PowerSeries.constantCoeff_C]
    refine ⟨ρ₀, hρ₀C, fun o => by rw [hτw o]; exact hρ₀C o, ?_⟩
    constructor
    intro a ha
    by_contra hna
    have hmem : a ∈ maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna)
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, rfl⟩ := hmem
    apply ha.ne_zero
    rw [map_mul, hπdef, hρ₀C ϖ, hredϖ, zero_mul]
  haveI := hρloc
  have hρπ : ρ π = 0 := by
    rw [hπdef, hρw]; exact (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩

  have hs : smulNodePair (arithFrobC q k N) w ∈ nodePairsOfPlaces (arithFrobC q k N) W₀ :=
    smulNodePair_mem_nodePairsOfPlaces _ hw
  have hregB : ∀ g : ↥(R.nodeIntegersOver K' w),
      0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) ∧
      0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) := by
    intro g
    obtain ⟨cv, hcv₁, hcv₂⟩ := hreg.2 (g : ↥(modularFunctionFieldBar (N * q))) g.2.1.1 g.2.1.2.1 _ hs
      (fun V' hV' => R.ord_nonneg_of_mem_nodeIntegers g.2.1 hV')
    exact ⟨w.ord_nonneg_of_mem hcv₁.mem, (arithFrobC q k N • w).ord_nonneg_of_mem hcv₂.mem⟩
  have hBinj : Function.Injective (algebraMap ↥(R.nodeIntegersOver K' w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K' w)) ↥(R.nodeIntegersOver K' w))) := by
    haveI : IsHausdorff (maximalIdeal ↥(R.nodeIntegersOver K' w)) ↥(R.nodeIntegersOver K' w) :=
      IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal _).ne_top
    exact AdicCompletion.of_injective (maximalIdeal ↥(R.nodeIntegersOver K' w)) ↥(R.nodeIntegersOver K' w)
  have hιne : ∀ g : ↥(R.nodeIntegersOver K' w), g ≠ 0 → ι (algebraMap _ _ g) ≠ 0 := by
    intro g hg h0
    apply hg
    apply hBinj
    rw [map_zero]
    exact ι.injective (by rw [h0, map_zero])

  have hc₁F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ ≠ 0 := (map_ne_zero _).mpr hc₁0
  have hc₂F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ ≠ 0 := (map_ne_zero _).mpr hc₂0
  have hg₁K : ((c₁ • f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K' := by
    rw [IntermediateField.coe_smul, Algebra.smul_def]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨⟨c₁, hc₁⟩, rfl⟩)) hfK
  have hg₂K : ((c₂ • f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K' := by
    rw [IntermediateField.coe_smul, Algebra.smul_def]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨⟨c₂, hc₂⟩, rfl⟩)) hfK
  obtain ⟨xx₁, yy₁, hxx₁, hyy₁, hyy₁0, hzz₁⟩ := hfrac _ hg₁K
  have hzz₁F : (c₁ • f) * yy₁ = xx₁ := by
    apply Subtype.ext; rw [MulMemClass.coe_mul]; exact hzz₁
  obtain ⟨a₁, b₁, hb₁, hfb₁⟩ :=
    exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero R K' w c' ϖ hϖ hmax hbr E hE u hu hxy' ⟨xx₁, hxx₁⟩ ⟨yy₁, hyy₁⟩
      (fun h => hyy₁0 (congrArg Subtype.val h)) (c₁ • f) h₁ hzz₁F
  obtain ⟨xx₂, yy₂, hxx₂, hyy₂, hyy₂0, hzz₂⟩ := hfrac _ hg₂K
  have hzz₂F : (c₂ • f) * yy₂ = xx₂ := by
    apply Subtype.ext; rw [MulMemClass.coe_mul]; exact hzz₂
  obtain ⟨a₂, b₂, hb₂, hfb₂⟩ :=
    exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero R K' w c' ϖ hϖ hmax hbr E hE u hu hxy' ⟨xx₂, hxx₂⟩ ⟨yy₂, hyy₂⟩
      (fun h => hyy₂0 (congrArg Subtype.val h)) (c₂ • f) h₂ hzz₂F

  have hb₁0 : b₁ ≠ 0 := by
    intro h0; apply hb₁
    have e : (⟨((b₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), b₁.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
      Subtype.ext (by rw [h0]; rfl)
    rw [e, map_zero]
  have hb₂0 : b₂ ≠ 0 := by
    intro h0; apply hb₂
    have e : (⟨((b₂ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
      Subtype.ext (by rw [h0]; rfl)
    rw [e, map_zero]
  have ha₁0 : a₁ ≠ 0 := by
    intro h0
    have : (c₁ • f) * (b₁ : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hfb₁, h0]; rfl
    rcases mul_eq_zero.mp this with h | h
    · rw [Algebra.smul_def] at h; exact (mul_ne_zero hc₁F hf) h
    · exact hb₁0 (Subtype.ext h)
  have ha₂0 : a₂ ≠ 0 := by
    intro h0
    have : (c₂ • f) * (b₂ : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hfb₂, h0]; rfl
    rcases mul_eq_zero.mp this with h | h
    · rw [Algebra.smul_def] at h; exact (mul_ne_zero hc₂F hf) h
    · exact hb₂0 (Subtype.ext h)
  have hu₁' : (R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0; apply hu₁; rwa [ProlongationTuple.residue₁_apply, map_eq_zero_iff _ R.ι.injective] at h0
  have hu₂' : (R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0; apply hu₂; rwa [ProlongationTuple.residue₂_apply, map_eq_zero_iff _ R.ι.injective] at h0

  have hres₁a : (R.nodeResidue₁ w ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1⟩ : ↥(modularFunctionFieldC k N))
      = R.residue₁ ⟨c₁ • f, h₁⟩ * R.nodeResidue₁ w ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1⟩ := by
    rw [nodeResidue₁_apply, nodeResidue₁_apply, ← map_mul]
    congr 1
    exact Subtype.ext hfb₁.symm
  have hres₂a : (R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N))
      = R.residue₂ ⟨c₂ • f, h₂⟩ * R.nodeResidue₂ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ := by
    rw [nodeResidue₂_apply, nodeResidue₂_apply, ← map_mul]
    congr 1
    exact Subtype.ext hfb₂.symm
  have ha₁ne : R.nodeResidue₁ w ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1⟩ ≠ 0 := by
    rw [hres₁a]; exact mul_ne_zero hu₁' hb₁
  have ha₂ne : R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ ≠ 0 := by
    rw [hres₂a]; exact mul_ne_zero hu₂' hb₂

  obtain ⟨o₁, ho₁⟩ : ∃ z : ℤ, z = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := ⟨_, rfl⟩
  obtain ⟨o₂, ho₂⟩ : ∃ z : ℤ, z = (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := ⟨_, rfl⟩
  obtain ⟨na, hna⟩ : ∃ n : ℕ, (n : ℤ) = w.ord (R.nodeResidue₁ w ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1⟩ : ↥(modularFunctionFieldC k N)) :=
    ⟨_, Int.toNat_of_nonneg (hregB a₁).1⟩
  obtain ⟨nb, hnb⟩ : ∃ n : ℕ, (n : ℤ) = w.ord (R.nodeResidue₁ w ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1⟩ : ↥(modularFunctionFieldC k N)) :=
    ⟨_, Int.toNat_of_nonneg (hregB b₁).1⟩
  obtain ⟨ma, hma⟩ : ∃ n : ℕ, (n : ℤ) = (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N)) :=
    ⟨_, Int.toNat_of_nonneg (hregB a₂).2⟩
  obtain ⟨mb, hmb⟩ : ∃ n : ℕ, (n : ℤ) = (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(modularFunctionFieldC k N)) :=
    ⟨_, Int.toNat_of_nonneg (hregB b₂).2⟩
  have ho₁ab : o₁ = na - nb := by
    rw [ho₁, hna, hnb, hres₁a, w.ord_mul hu₁' hb₁]; ring
  have ho₂ab : o₂ = ma - mb := by
    rw [ho₂, hma, hmb, hres₂a, (arithFrobC q k N • w).ord_mul hu₂' hb₂]; ring

  obtain ⟨A₁, hA₁⟩ : ∃ z, z = ι (algebraMap _ _ a₁) := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ z, z = ι (algebraMap _ _ b₁) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ z, z = ι (algebraMap _ _ a₂) := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ z, z = ι (algebraMap _ _ b₂) := ⟨_, rfl⟩
  have hA₁0 : A₁ ≠ 0 := hA₁ ▸ hιne a₁ ha₁0
  have hB₁0 : B₁ ≠ 0 := hB₁ ▸ hιne b₁ hb₁0
  have hA₂0 : A₂ ≠ 0 := hA₂ ▸ hιne a₂ ha₂0
  have hB₂0 : B₂ ≠ 0 := hB₂ ▸ hιne b₂ hb₂0
  obtain ⟨nfA₁, hnfA₁, -⟩ := existsUnique_normalForm π E hE A₁
  obtain ⟨nfB₁, hnfB₁, -⟩ := existsUnique_normalForm π E hE B₁
  obtain ⟨nfA₂, hnfA₂, -⟩ := existsUnique_normalForm π E hE A₂
  obtain ⟨nfB₂, hnfB₂, -⟩ := existsUnique_normalForm π E hE B₂

  obtain ⟨Gα, hGα⟩ := mk_surjective (π ^ E) αU
  obtain ⟨Gβ, hGβ⟩ := mk_surjective (π ^ E) βV

  obtain ⟨γa₁, hγa₁, hra₁⟩ := hιord₁ a₁ na ha₁ne hna.symm
  obtain ⟨γb₁, hγb₁, hrb₁⟩ := hιord₁ b₁ nb hb₁ hnb.symm
  obtain ⟨γa₂, hγa₂, hra₂⟩ := hιord₂ a₂ ma ha₂ne hma.symm
  obtain ⟨γb₂, hγb₂, hrb₂⟩ := hιord₂ b₂ mb hb₂ hmb.symm
  obtain ⟨Ga₁, hGa₁⟩ := mk_surjective (π ^ E) γa₁
  obtain ⟨Gb₁, hGb₁⟩ := mk_surjective (π ^ E) γb₁
  obtain ⟨Ga₂, hGa₂⟩ := mk_surjective (π ^ E) γa₂
  obtain ⟨Gb₂, hGb₂⟩ := mk_surjective (π ^ E) γb₂
  have hEa₁ := Ws12NodeTel.endV_eq_and_lrV_eq_of_sub_mul_V_pow_mem π hπ E hE A₁ hA₁0 nfA₁ hnfA₁.1 hnfA₁.2 γa₁ hγa₁ na (hA₁ ▸ hra₁) Ga₁ hGa₁
  have hEb₁ := Ws12NodeTel.endV_eq_and_lrV_eq_of_sub_mul_V_pow_mem π hπ E hE B₁ hB₁0 nfB₁ hnfB₁.1 hnfB₁.2 γb₁ hγb₁ nb (hB₁ ▸ hrb₁) Gb₁ hGb₁
  have hEa₂ := Ws12NodeTel.endU_eq_and_lrU_eq_of_sub_mul_U_pow_mem π hπ E hE A₂ hA₂0 nfA₂ hnfA₂.1 hnfA₂.2 γa₂ hγa₂ ma (hA₂ ▸ hra₂) Ga₂ hGa₂
  have hEb₂ := Ws12NodeTel.endU_eq_and_lrU_eq_of_sub_mul_U_pow_mem π hπ E hE B₂ hB₂0 nfB₂ hnfB₂.1 hnfB₂.2 γb₂ hγb₂ mb (hB₂ ▸ hrb₂) Gb₂ hGb₂

  let wmap : ↥(coeffSubring A K') →+* (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) :=
    (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ})).comp PowerSeries.C
  have hwϖ : wmap ϖ = π := rfl
  have hιw : ∀ o : ↥(coeffSubring A K'), ι (algebraMap _ _ (R.nodeConst K' w o)) = const (π ^ E) (wmap o) := hιo
  have hρw' : ∀ o : ↥(coeffSubring A K'), ρ (wmap o) = redRestrict red K' o := hρw

  obtain ⟨V₀, hV₀⟩ := Ws12NodeTel.exists_place_reduceFst_eq R hqN hmodel w hwss
  have hVAL₁ := fun (g : ↥(R.nodeIntegersOver K' w)) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (hV : P.reduceFst V = w) =>
    hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed R hqN hmodel hO W₀ hW₀ hreg hval K' w hw hVI g V hV
  have hVAL₂ := fun (g : ↥(R.nodeIntegersOver K' w)) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (hV : P.reduceFst V = w) =>
    hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed R hqN hmodel hO W₀ hW₀ hreg hval K' w hw hVI g V hV
  have hva₁ := hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue R K' w c' ϖ hmax' hres hϖ hVI hwss
    π hπ E hE ι wmap hwϖ hιw ρ hρw' V₀ hV₀ hVAL₁ βV hβV hιy αU hαU hιx Gβ hGβ
    a₁ na ha₁ne hna.symm γa₁ hγa₁ hra₁ Ga₁ hGa₁
  have hvb₁ := hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue R K' w c' ϖ hmax' hres hϖ hVI hwss
    π hπ E hE ι wmap hwϖ hιw ρ hρw' V₀ hV₀ hVAL₁ βV hβV hιy αU hαU hιx Gβ hGβ
    b₁ nb hb₁ hnb.symm γb₁ hγb₁ hrb₁ Gb₁ hGb₁
  have hva₂ := hasValue_nodeResidueSnd_div_nodeResidueSnd_x_pow_of_sub_mul_U_pow_mem_of_hasValue R K' w c' ϖ hmax' hres hϖ hVI hwss
    π hπ E hE ι wmap hwϖ hιw ρ hρw' V₀ hV₀ hVAL₂ αU hαU hιx βV hβV hιy Gα hGα
    a₂ ma ha₂ne hma.symm γa₂ hγa₂ hra₂ Ga₂ hGa₂
  have hvb₂ := hasValue_nodeResidueSnd_div_nodeResidueSnd_x_pow_of_sub_mul_U_pow_mem_of_hasValue R K' w c' ϖ hmax' hres hϖ hVI hwss
    π hπ E hE ι wmap hwϖ hιw ρ hρw' V₀ hV₀ hVAL₂ αU hαU hιx βV hβV hιy Gα hGα
    b₂ mb hb₂ hmb.symm γb₂ hγb₂ hrb₂ Gb₂ hGb₂

  haveI hRdom : IsDomain (UVCrossingModel (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (π ^ E)) :=
    (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE).1
  have hιu : ι (algebraMap _ _ u) = αU * βV := by
    have h := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => ι (algebraMap _ _ z)) hxy'
    simp only [map_mul, map_pow] at h
    rw [hιx, hιy, hιϖ] at h
    have h2 : const (π ^ E) π ^ E * (αU * βV) = const (π ^ E) π ^ E * ι (algebraMap _ _ u) := by
      rw [← h, show U (π ^ E) * αU * (V (π ^ E) * βV) = (U (π ^ E) * V (π ^ E)) * (αU * βV) by ring,
        Ws12NodeTel.U_mul_V_eq]
    exact (mul_left_cancel₀ (pow_ne_zero E (Ws12NodeTel.const_ne_zero π hπ E hE π hπ.ne_zero)) h2).symm

  have hu0' : (u0 : k) = ρ (MvPowerSeries.constantCoeff Gα) * ρ (MvPowerSeries.constantCoeff Gβ) := by
    have hune : R.nodeResidue₁ w ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩ ≠ 0 := hu0.ne_zero (Units.ne_zero u0)
    have hord : w.ord (R.nodeResidue₁ w ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩) = ((0 : ℕ) : ℤ) := by
      rw [Nat.cast_zero]; exact hu0.ord_eq_zero (Units.ne_zero u0)
    have hfγ : ι (algebraMap _ _ u) - αU * βV * V (π ^ E) ^ 0 ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
      rw [pow_zero, mul_one, hιu, sub_self]; exact Ideal.zero_mem _
    have hv := hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue R K' w c' ϖ hmax' hres hϖ hVI hwss
      π hπ E hE ι wmap hwϖ hιw ρ hρw' V₀ hV₀ hVAL₁ βV hβV hιy αU hαU hιx Gβ hGβ
      u 0 hune hord (αU * βV) (hαU.mul hβV) hfγ (Gα * Gβ) (by rw [map_mul, hGα, hGβ])
    rw [pow_zero, div_one, pow_zero, mul_one, map_mul, map_mul] at hv
    exact hu0.unique hv

  have hπnu : ¬ IsUnit π := hπ.not_isUnit
  have hρunit : ∀ G : MvPowerSeries (Fin 2) (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}),
      IsUnit (mk (π ^ E) G) → ρ (MvPowerSeries.constantCoeff G) ≠ 0 := by
    intro G hG h0
    have hu := Ws12NodeTel.isUnit_constantCoeff_of_isUnit_mk π E hE hπnu G hG
    exact (hu.map ρ).ne_zero h0
  have hρa₁ := hρunit Ga₁ (hGa₁ ▸ hγa₁)
  have hρb₁ := hρunit Gb₁ (hGb₁ ▸ hγb₁)
  have hρa₂ := hρunit Ga₂ (hGa₂ ▸ hγa₂)
  have hρb₂ := hρunit Gb₂ (hGb₂ ▸ hγb₂)
  have hρα := hρunit Gα (hGα ▸ hαU)
  have hρβ := hρunit Gβ (hGβ ▸ hβV)

  have hybar0 : (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 :=
    c.nodeResidue₁_y_ne_zero
  have hxbar0 : (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 :=
    c.nodeResidue₂_x_ne_zero
  have hvb₁0 : ρ (MvPowerSeries.constantCoeff Gb₁) * (ρ (MvPowerSeries.constantCoeff Gβ))⁻¹ ^ nb ≠ 0 :=
    mul_ne_zero hρb₁ (pow_ne_zero _ (inv_ne_zero hρβ))
  have hva₁0 : ρ (MvPowerSeries.constantCoeff Ga₁) * (ρ (MvPowerSeries.constantCoeff Gβ))⁻¹ ^ na ≠ 0 :=
    mul_ne_zero hρa₁ (pow_ne_zero _ (inv_ne_zero hρβ))
  have hvb₂0 : ρ (MvPowerSeries.constantCoeff Gb₂) * (ρ (MvPowerSeries.constantCoeff Gα))⁻¹ ^ mb ≠ 0 :=
    mul_ne_zero hρb₂ (pow_ne_zero _ (inv_ne_zero hρα))
  have hva₂0 : ρ (MvPowerSeries.constantCoeff Ga₂) * (ρ (MvPowerSeries.constantCoeff Gα))⁻¹ ^ ma ≠ 0 :=
    mul_ne_zero hρa₂ (pow_ne_zero _ (inv_ne_zero hρα))
  have hV₁ := hva₁.mul (hvb₁.inv hvb₁0)
  have hV₂ := hva₂.mul (hvb₂.inv hvb₂0)

  have hres₁f : (R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) =
      (R.nodeResidue₁ w ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1⟩ : ↥(modularFunctionFieldC k N)) /
        (R.nodeResidue₁ w ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1⟩ : ↥(modularFunctionFieldC k N)) := by
    rw [eq_div_iff hb₁, hres₁a]
  have hres₂f : (R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) =
      (R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N)) /
        (R.nodeResidue₂ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(modularFunctionFieldC k N)) := by
    rw [eq_div_iff hb₂, hres₂a]
  have hfun₁ : (R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) /
        (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ^
          (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)) =
      (R.nodeResidue₁ w ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ^ na *
        ((R.nodeResidue₁ w ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ^ nb)⁻¹ := by
    rw [← ho₁, ho₁ab, hres₁f, zpow_sub₀ hybar0, zpow_natCast, zpow_natCast]
    field_simp
  have hfun₂ : (R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) /
        (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ^
          ((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) =
      (R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ^ ma *
        ((R.nodeResidue₂ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ^ mb)⁻¹ := by
    rw [← ho₂, ho₂ab, hres₂f, zpow_sub₀ hxbar0, zpow_natCast, zpow_natCast]
    field_simp
  refine ⟨Units.mk0 _ (mul_ne_zero hva₁0 (inv_ne_zero hvb₁0)), Units.mk0 _ (mul_ne_zero hva₂0 (inv_ne_zero hvb₂0)), ?_, ?_, ?_⟩
  · rw [Units.val_mk0, hfun₁]; exact hV₁
  · rw [Units.val_mk0, hfun₂]; exact hV₂

  have hρk : ∀ z, IsLocalRing.ResidueField.lift ρ (IsLocalRing.residue _ z) = ρ z :=
    fun z => IsLocalRing.ResidueField.lift_residue_apply ρ z
  have hra₁ : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrV π E nfA₁) = ρ (MvPowerSeries.constantCoeff Ga₁) := by
    rw [hEa₁.2, hρk]
  have hrb₁ : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrV π E nfB₁) = ρ (MvPowerSeries.constantCoeff Gb₁) := by
    rw [hEb₁.2, hρk]
  have hra₂ : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfA₂) = ρ (MvPowerSeries.constantCoeff Ga₂) := by
    rw [hEa₂.2, hρk]
  have hrb₂ : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfB₂) = ρ (MvPowerSeries.constantCoeff Gb₂) := by
    rw [hEb₂.2, hρk]

  have hF1 : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfA₁) * ρ (MvPowerSeries.constantCoeff Gb₂) * (ηbar₂ : k) =
      ρ (MvPowerSeries.constantCoeff Ga₂) * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfB₁) * (ηbar₁ : k) := by

    obtain ⟨M, hM₁, hM₂⟩ : ∃ M : ℕ, 0 ≤ (M : ℤ) + m₁ ∧ 0 ≤ (M : ℤ) + m₂ :=
      ⟨(max (-m₁) (-m₂)).toNat, by have := Int.self_le_toNat (max (-m₁) (-m₂)); omega,
        by have := Int.self_le_toNat (max (-m₁) (-m₂)); omega⟩
    obtain ⟨k₁, hk₁⟩ : ∃ k : ℕ, (k : ℤ) = (M : ℤ) + m₁ := ⟨_, Int.toNat_of_nonneg hM₁⟩
    obtain ⟨k₂, hk₂⟩ : ∃ k : ℕ, (k : ℤ) = (M : ℤ) + m₂ := ⟨_, Int.toNat_of_nonneg hM₂⟩
    have hϖ0 : ((ϖ : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖirr.ne_zero (Subtype.ext h)
    have hcM : ∀ (cc : AlgebraicClosure ℚ) (mm : ℤ) (kk : ℕ) (η : ↥(coeffSubring A K')),
        cc = ((ϖ : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ^ mm * (η : AlgebraicClosure ℚ) → (kk : ℤ) = (M : ℤ) + mm →
        ((ϖ : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ^ M * cc =
          (((ϖ ^ kk : ↥(coeffSubring A K')) : AlgebraicClosure ℚ)) * (η : AlgebraicClosure ℚ) := by
      intro cc mm kk η hcc hkk
      rw [hcc, Subring.coe_pow, ← zpow_natCast, ← zpow_natCast, hkk, zpow_add₀ hϖ0]; ring

    have hidB : a₁ * b₂ * R.nodeConst K' w (ϖ ^ k₂ * η₂) = a₂ * b₁ * R.nodeConst K' w (ϖ ^ k₁ * η₁) := by
      apply Subtype.ext
      simp only [Subring.coe_mul, ProlongationTuple.coe_nodeConst]
      rw [← hcM c₂ m₂ k₂ η₂ hc₂η hk₂, ← hcM c₁ m₁ k₁ η₁ hc₁η hk₁, ← hfb₁, ← hfb₂, map_mul, map_mul, map_pow,
        Algebra.smul_def, Algebra.smul_def]
      ring

    have hwη : ∀ η : ↥(coeffSubring A K'), IsUnit η → IsUnit (wmap η) := fun η hη => hη.map wmap
    have hidM : A₁ * B₂ * const (π ^ E) (π ^ k₂ * wmap η₂) = A₂ * B₁ * const (π ^ E) (π ^ k₁ * wmap η₁) := by
      have h := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => ι (algebraMap _ _ z)) hidB
      simp only [map_mul, map_pow, hιw, hwϖ, hιϖ] at h
      rw [← hA₁, ← hB₂, ← hA₂, ← hB₁] at h
      rw [← constHom_apply, ← constHom_apply, map_mul, map_mul, map_pow, map_pow, constHom_apply, constHom_apply, constHom_apply]
      exact h

    have hw₁0 : π ^ k₁ * wmap η₁ ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (hwη η₁ hη₁).ne_zero
    have hw₂0 : π ^ k₂ * wmap η₂ ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (hwη η₂ hη₂).ne_zero
    have hC₁ := Ws12NodeTel.normalForm_const π E (π ^ k₁ * wmap η₁)
    have hC₂ := Ws12NodeTel.normalForm_const π E (π ^ k₂ * wmap η₂)
    have hc₁0 : const (π ^ E) (π ^ k₁ * wmap η₁) ≠ 0 := Ws12NodeTel.const_ne_zero π hπ E hE _ hw₁0
    have hc₂0 : const (π ^ E) (π ^ k₂ * wmap η₂) ≠ 0 := Ws12NodeTel.const_ne_zero π hπ E hE _ hw₂0
    obtain ⟨nf12, hnf12, -⟩ := existsUnique_normalForm π E hE (A₁ * B₂)
    obtain ⟨nf21, hnf21, -⟩ := existsUnique_normalForm π E hE (A₂ * B₁)
    obtain ⟨nfL, hnfL, huL⟩ := existsUnique_normalForm π E hE (A₁ * B₂ * const (π ^ E) (π ^ k₂ * wmap η₂))
    have h12 := Ws12NodeTel.lrU_mul π hπ E hE A₁ hA₁0 nfA₁ hnfA₁.1 hnfA₁.2 B₂ hB₂0 nfB₂ hnfB₂.1 hnfB₂.2 nf12 hnf12.1 hnf12.2
    have h21 := Ws12NodeTel.lrU_mul π hπ E hE A₂ hA₂0 nfA₂ hnfA₂.1 hnfA₂.2 B₁ hB₁0 nfB₁ hnfB₁.1 hnfB₁.2 nf21 hnf21.1 hnf21.2
    have hL := Ws12NodeTel.lrU_mul π hπ E hE (A₁ * B₂) (mul_ne_zero hA₁0 hB₂0) nf12 hnf12.1 hnf12.2 _ hc₂0 _ hC₂.1 hC₂.2
      nfL hnfL.1 hnfL.2
    have hR := Ws12NodeTel.lrU_mul π hπ E hE (A₂ * B₁) (mul_ne_zero hA₂0 hB₁0) nf21 hnf21.1 hnf21.2 _ hc₁0 _ hC₁.1 hC₁.2
      nfL hnfL.1 (hnfL.2.trans hidM)
    rw [h12, Ws12NodeTel.lrU_const π E hE _ hw₂0, Ws12NodeTel.leadingResidue_pow_mul π hπ k₂ _ (hwη η₂ hη₂).ne_zero,
      Ws12NodeTel.leadingResidue_of_isUnit π hπ _ (hwη η₂ hη₂)] at hL
    rw [h21, Ws12NodeTel.lrU_const π E hE _ hw₁0, Ws12NodeTel.leadingResidue_pow_mul π hπ k₁ _ (hwη η₁ hη₁).ne_zero,
      Ws12NodeTel.leadingResidue_of_isUnit π hπ _ (hwη η₁ hη₁)] at hR
    have h := congrArg (IsLocalRing.ResidueField.lift ρ) (hL.symm.trans hR)
    rw [map_mul, map_mul, map_mul, map_mul, hρk, hρk, hrb₂, hra₂, hρw', hρw', hηbar₁, hηbar₂] at h
    exact h

  have hF2a : ρ (MvPowerSeries.constantCoeff Ga₁) * Ws12NodeTel.normProdK ρ π E A₁ =
      (-1) ^ (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfA₁) := by
    have h := congrArg (IsLocalRing.ResidueField.lift ρ) (Ws12NodeTel.lrV_mul_normProd_eq π hπ E hE A₁ hA₁0 nfA₁ hnfA₁.1 hnfA₁.2)
    have hl : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrV π E nfA₁ * Ws12NodeTel.normProd π E A₁) =
        IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrV π E nfA₁) * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.normProd π E A₁) := map_mul _ _ _
    have hr : IsLocalRing.ResidueField.lift ρ ((-1) ^ (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat * Ws12NodeTel.lrU π E nfA₁) =
        (-1) ^ (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfA₁) := by
      simp only [map_mul, map_pow, map_neg, map_one]
    rw [hl, hr, hra₁, Ws12NodeTel.lift_normProd ρ π hπ E hE A₁ hA₁0] at h
    exact h
  have hF2b : ρ (MvPowerSeries.constantCoeff Gb₁) * Ws12NodeTel.normProdK ρ π E B₁ =
      (-1) ^ (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfB₁) := by
    have h := congrArg (IsLocalRing.ResidueField.lift ρ) (Ws12NodeTel.lrV_mul_normProd_eq π hπ E hE B₁ hB₁0 nfB₁ hnfB₁.1 hnfB₁.2)
    have hl : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrV π E nfB₁ * Ws12NodeTel.normProd π E B₁) =
        IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrV π E nfB₁) * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.normProd π E B₁) := map_mul _ _ _
    have hr : IsLocalRing.ResidueField.lift ρ ((-1) ^ (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat * Ws12NodeTel.lrU π E nfB₁) =
        (-1) ^ (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat * IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfB₁) := by
      simp only [map_mul, map_pow, map_neg, map_one]
    rw [hl, hr, hrb₁, Ws12NodeTel.lift_normProd ρ π hπ E hE B₁ hB₁0] at h
    exact h

  have hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K' w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K' w) → 𝔭 < 𝔮 → 𝔭 = ⊥ :=
    IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
      (R := UVCrossingModel (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (π ^ E))
      ι (by exact ringKrullDim_le_two π hπ E hE)
  obtain ⟨jC, hjC⟩ := ModularCurve.PlaceSpecialization.exists_ringHom_adicCompletion_coeffSubring_valuationInteger (A := A) K'
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨Da, hDa, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    ((a₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) (fun h => ha₁0 (Subtype.ext h))
  obtain ⟨Db, hDb, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    ((b₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) (fun h => hb₁0 (Subtype.ext h))
  have hTa : ∀ V, V ∈ Da.support.filter (fun V => P.reduceFst V = w) ↔
      (V.ord ((a₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 ∧ P.reduceFst V = w) := by
    intro V; rw [Finset.mem_filter, Finsupp.mem_support_iff, hDa]
  have hTb : ∀ V, V ∈ Db.support.filter (fun V => P.reduceFst V = w) ↔
      (V.ord ((b₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 ∧ P.reduceFst V = w) := by
    intro V; rw [Finset.mem_filter, Finsupp.mem_support_iff, hDb]
  have hF3a := Ws12NodeTel.exists_red_prod_evalAt_y_pow_ord_eq R K' w c' ϖ hϖirr.ne_zero hmax' hres hVI hwss π hπ E hE ι hιϖ
    αU hαU hιx hht hfrac hϖgen τ hτ hτϖ jC hjC βV hβV hιy hqN hO hιord₁ hιord₂ ρ hρτ Gβ hGβ
    a₁ ha₁0 nfA₁ hnfA₁.1 (hnfA₁.2.trans hA₁) _ hTa
  have hF3b := Ws12NodeTel.exists_red_prod_evalAt_y_pow_ord_eq R K' w c' ϖ hϖirr.ne_zero hmax' hres hVI hwss π hπ E hE ι hιϖ
    αU hαU hιx hht hfrac hϖgen τ hτ hτϖ jC hjC βV hβV hιy hqN hO hιord₁ hιord₂ ρ hρτ Gβ hGβ
    b₁ hb₁0 nfB₁ hnfB₁.1 (hnfB₁.2.trans hB₁) _ hTb
  obtain ⟨hcnta, sa, hmema, hreda⟩ := hF3a
  obtain ⟨hcntb, sb, hmemb, hredb⟩ := hF3b

  have hfilt : ∀ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      X.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) =
        X.support.filter (fun V => P.reduceFst V = w) := by
    intro X
    apply Finset.filter_congr
    intro V _
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, Ws12NodeTel.not_isStrictFst_and_not_isStrictSnd_of_reduceFst_eq hqN w hwss V h⟩
  have hordf : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      D V = Da V - Db V := by
    intro V
    rw [hDf, hDa, hDb]
    exact Ws12NodeTel.ord_eq_ord_sub_ord_of_smul_mul_eq f _ _ c₁ hc₁0 hf (fun h => hb₁0 (Subtype.ext h)) hfb₁ V

  have hsumTa : (∑ V ∈ Da.support with P.reduceFst V = w, Da V) = Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁ := by
    rw [← hcnta, Nat.cast_sum]
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [Finset.mem_filter] at hV
    rw [hDa, Int.toNat_of_nonneg (R.ord_nonneg_of_mem_nodeIntegers a₁.2.1 hV.2)]
  have hsumTb : (∑ V ∈ Db.support with P.reduceFst V = w, Db V) = Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁ := by
    rw [← hcntb, Nat.cast_sum]
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [Finset.mem_filter] at hV
    rw [hDb, Int.toNat_of_nonneg (R.ord_nonneg_of_mem_nodeIntegers b₁.2.1 hV.2)]
  have hF5 : (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V) =
      (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁) - (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁) := by
    rw [hfilt, Ws12NodeTel.sum_filter_support_eq_sub D Db Da hordf P.reduceFst w, hsumTa, hsumTb]

  have hF4 : (Θ : k) * (Ws12NodeTel.normProdK ρ π E A₁ *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat) =
      ((εbar ^ m : kˣ) : k) * (Ws12NodeTel.normProdK ρ π E B₁ *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat) := by
    obtain ⟨hmemΘ, hredΘ⟩ := hΘ

    have hyne : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 := by
      intro V hV h0
      obtain ⟨hpos, hdep⟩ := hdepthQ V hV (Ws12NodeTel.not_isStrictFst_and_not_isStrictSnd_of_reduceFst_eq hqN w hwss V hV).1
        (Ws12NodeTel.not_isStrictFst_and_not_isStrictSnd_of_reduceFst_eq hqN w hwss V hV).2
      have hq0 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
      have hy0 : c.yDepth V = 0 := by
        show A.valuation (V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q))))) = 0
        rw [h0, Valuation.map_zero]
      rw [hy0, zero_pow (Rat.den_pos _).ne'] at hdep
      exact pow_ne_zero _ hq0 hdep.symm

    have hprod : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
        V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^ (-(D V))) =
        (∏ V ∈ Db.support with P.reduceFst V = w, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
            (V.ord ((b₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))).toNat) /
          ∏ V ∈ Da.support with P.reduceFst V = w, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
            (V.ord ((a₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))).toNat := by
      rw [hfilt, Ws12NodeTel.prod_filter_support_zpow_neg_eq_div D Db Da hordf P.reduceFst w _ hyne]
      congr 1
      · refine Finset.prod_congr rfl fun V hV => ?_
        rw [Finset.mem_filter] at hV
        rw [← zpow_natCast, hDb, Int.toNat_of_nonneg (R.ord_nonneg_of_mem_nodeIntegers b₁.2.1 hV.2)]
      · refine Finset.prod_congr rfl fun V hV => ?_
        rw [Finset.mem_filter] at hV
        rw [← zpow_natCast, hDa, Int.toNat_of_nonneg (R.ord_nonneg_of_mem_nodeIntegers a₁.2.1 hV.2)]

    have hRA0 : Ws12NodeTel.normProdK ρ π E A₁ * ρ (MvPowerSeries.constantCoeff Gβ) ^ (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ hρβ)
      intro h0
      have h := hF2a
      rw [h0, mul_zero] at h
      exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        ((map_ne_zero _).mpr (Ws12NodeTel.lrU_ne_zero π hπ E hE A₁ hA₁0 nfA₁ hnfA₁.1 hnfA₁.2))) h.symm
    have hRB0 : Ws12NodeTel.normProdK ρ π E B₁ * ρ (MvPowerSeries.constantCoeff Gβ) ^ (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ hρβ)
      intro h0
      have h := hF2b
      rw [h0, mul_zero] at h
      exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        ((map_ne_zero _).mpr (Ws12NodeTel.lrU_ne_zero π hπ E hE B₁ hB₁0 nfB₁ hnfB₁.1 hnfB₁.2))) h.symm
    have hεA : red ⟨(ε : AlgebraicClosure ℚ), ε.2.1⟩ = (εbar : k) := hεbar
    have hε0 : red ⟨(ε : AlgebraicClosure ℚ), ε.2.1⟩ ≠ 0 := by rw [hεA]; exact Units.ne_zero εbar
    obtain ⟨mp, mn, hm⟩ : ∃ mp mn : ℕ, m = (mp : ℤ) - (mn : ℤ) := ⟨m.toNat, (-m).toNat, by omega⟩
    set X₁ : A := ⟨_, hmemΘ⟩ * ⟨_, hmema⟩ * ⟨(ε : AlgebraicClosure ℚ), ε.2.1⟩ ^ mn with hX₁
    set X₂ : A := ⟨_, hmemb⟩ * ⟨(ε : AlgebraicClosure ℚ), ε.2.1⟩ ^ mp with hX₂
    have hX₁r : red X₁ = (Θ : k) * (Ws12NodeTel.normProdK ρ π E A₁ *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ (Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat) * (εbar : k) ^ mn := by
      rw [hX₁, map_mul, map_mul, map_pow, hredΘ, hreda, hεA, ← hA₁]
    have hX₂r : red X₂ = (Ws12NodeTel.normProdK ρ π E B₁ *
        ρ (MvPowerSeries.constantCoeff Gβ) ^ (Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat) * (εbar : k) ^ mp := by
      rw [hX₂, map_mul, map_pow, hredb, hεA, ← hB₁]
    have hX₁0 : red X₁ ≠ 0 := by rw [hX₁r]; exact mul_ne_zero (mul_ne_zero (Units.ne_zero Θ) hRA0) (pow_ne_zero _ (Units.ne_zero εbar))
    have hX₂0 : red X₂ ≠ 0 := by rw [hX₂r]; exact mul_ne_zero hRB0 (pow_ne_zero _ (Units.ne_zero εbar))
    have hϖ0 : ((ϖ : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖirr.ne_zero (Subtype.ext h)
    have hϖmA : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← hker]; exact (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
    have hqL : ((q : ℕ) : AlgebraicClosure ℚ) = ((ϖ : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
      have := congrArg (fun z : ↥(coeffSubring A K') => (z : AlgebraicClosure ℚ)) hqϖ
      simpa using this
    have hPa0 : (∏ V ∈ Da.support with P.reduceFst V = w, V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^
        (V.ord ((a₁ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))).toNat) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun V hV => pow_ne_zero _ (hyne V (Finset.mem_filter.mp hV).2)
    have hεL0 : ((ε : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ≠ 0 := fun h => hε.ne_zero (Subtype.ext h)
    have hrel : (X₁ : AlgebraicClosure ℚ) = ((⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) : AlgebraicClosure ℚ) ^ ((eK : ℤ) * m - sa + sb) * (X₂ : AlgebraicClosure ℚ) := by
      rw [hX₁, hX₂]
      push_cast
      rw [hprod, hqL]
      exact Ws12NodeTel.theta_exponent_identity _ _ _ _ hPa0 hϖ0 hεL0 eK sa sb mp mn m hm
    have hkey := Ws12NodeTel.red_eq_red_of_eq_zpow_mul red hker ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ hϖmA hϖ0 X₁ X₂ hX₁0 hX₂0 _ hrel
    rw [hX₁r, hX₂r] at hkey

    rw [Units.val_zpow_eq_zpow_val, hm, zpow_sub₀ (Units.ne_zero εbar), zpow_natCast, zpow_natCast]
    field_simp
    linear_combination hkey
  have hF5' : (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V) = o₁ + o₂ := by
    rw [hN, ← ho₁, ← ho₂]

  have hdegZ : o₁ + o₂ = ((Ws12NodeTel.endU E nfA₁ - Ws12NodeTel.endV E nfA₁).toNat : ℤ) -
      ((Ws12NodeTel.endU E nfB₁ - Ws12NodeTel.endV E nfB₁).toNat : ℤ) := by
    have h := hF5.symm.trans hF5'
    rw [Int.toNat_of_nonneg (Ws12NodeTel.endU_sub_endV_eq_finsum π hπ E hE A₁ hA₁0 nfA₁ hnfA₁.1 hnfA₁.2).1,
      Int.toNat_of_nonneg (Ws12NodeTel.endU_sub_endV_eq_finsum π hπ E hE B₁ hB₁0 nfB₁ hnfB₁.1 hnfB₁.2).1]
    linarith
  have hua₁0 : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfA₁) ≠ 0 :=
    (map_ne_zero _).mpr (Ws12NodeTel.lrU_ne_zero π hπ E hE A₁ hA₁0 nfA₁ hnfA₁.1 hnfA₁.2)
  have hub₁0 : IsLocalRing.ResidueField.lift ρ (Ws12NodeTel.lrU π E nfB₁) ≠ 0 :=
    (map_ne_zero _).mpr (Ws12NodeTel.lrU_ne_zero π hπ E hE B₁ hB₁0 nfB₁ hnfB₁.1 hnfB₁.2)
  have hnPa0 : Ws12NodeTel.normProdK ρ π E A₁ ≠ 0 := by
    intro h0; apply hua₁0
    have h := hF2a; rw [h0, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  have hnPb0 : Ws12NodeTel.normProdK ρ π E B₁ ≠ 0 := by
    intro h0; apply hub₁0
    have h := hF2b; rw [h0, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  rw [Units.val_zpow_eq_zpow_val] at hF4
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one,
    Units.val_pow_eq_pow_val]
  rw [hF5', ← ho₂]
  exact Ws12NodeTel.nodeTel_final_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hρb₁ hρa₂ hρb₂ hρα hρβ hua₁0 hub₁0 hnPa0 hnPb0
    (Units.ne_zero ηbar₁) (Units.ne_zero ηbar₂) (Units.ne_zero Θ) (Units.ne_zero εbar) _ _ na nb ma mb o₁ o₂ m
    hF1 hF2a hF2b hF4 hdegZ ho₁ab ho₂ab hu0'

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable (solution)
