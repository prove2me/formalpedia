-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1201de76-ec7e-5670-9387-004699b8f6bc

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_ratFunc
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Theorems.Thm_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin
import Theorems.Thm_ModularCurve_DRModelPackage_range_compInf_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel"

open scoped TensorProduct

noncomputable section

namespace GLUECI

open AlgebraicCurve.TwoChartIntegralModel

structure GlueDatum (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) where
  θFin : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(chartRing κ ({t} : Set L))
  θInf : ↥(chartAlgInf R F j) ⊗[R] κ →+* ↥(chartRing κ ({t⁻¹} : Set L))
  ρMid : ↥(chartAlgMid R F j) →+* ↥(chartRing κ ({t, t⁻¹} : Set L))
  θFin_right : θFin.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgFin R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t} : Set L))
  θInf_right : θInf.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgInf R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L))
  sq_fin : (incl₀ κ t).toRingHom.comp (θFin.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (TwoChartIntegralModel.inclFin R F j).toRingHom
  sq_inf : (CurveModel.inclInf κ t).toRingHom.comp (θInf.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (TwoChartIntegralModel.inclInf R F j).toRingHom
  m : ℕ
  m_pos : 0 < m
  ρFin_j : (θFin.comp Algebra.TensorProduct.includeLeftRingHom) (jChartFin R F j) = tChart κ t ^ m
  ρInf_jInv : (θInf.comp Algebra.TensorProduct.includeLeftRingHom) (jInvChartInf R F j) = tInvChart κ t ^ m
  surjFin : Function.Surjective θFin
  surjInf : Function.Surjective θInf

abbrev baseMap (R : Type u) [CommRing R] (κ : Type u) [Field κ] [Algebra R κ] :
    Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R κ))

section Model

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem tc_ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : TwoChartIntegralModel.XInf R F j) :
    (ιFin R F j).base x₀ = (TwoChartIntegralModel.ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (TwoChartIntegralModel.fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (fFin R F j) (TwoChartIntegralModel.fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w =
      (TwoChartIntegralModel.fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base w
    rw [TwoChartIntegralModel.glue_condition]

theorem tc_range_fInf : Set.range (TwoChartIntegralModel.fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf R F j))) : Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (TwoChartIntegralModel.inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jInvChartInf R F j)

theorem tc_ιInf_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔
      jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (tc_ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (tc_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem tc_range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgFin R F j))) : Set (PrimeSpectrum ↥(chartAlgFin R F j))) := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jChartFin R F j)

theorem tc_ιFin_mem_range_ιInf_iff (x₀ : XFin R F j) :
    (ιFin R F j).base x₀ ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (tc_ιFin_eq_ιInf_iff R F j x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fInf R F j).base w, ((tc_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

end Model

section Schemes

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]
  (D : GlueDatum R F j κ t)

abbrev GlueDatum.ρFin : ↥(chartAlgFin R F j) →+* ↥(chartRing κ ({t} : Set L)) :=
  D.θFin.comp Algebra.TensorProduct.includeLeftRingHom

abbrev GlueDatum.ρInf : ↥(chartAlgInf R F j) →+* ↥(chartRing κ ({t⁻¹} : Set L)) :=
  D.θInf.comp Algebra.TensorProduct.includeLeftRingHom

theorem ρFin_comp_algebraMap :
    D.ρFin.comp (algebraMap R ↥(chartAlgFin R F j)) =
      (algebraMap κ ↥(chartRing κ ({t} : Set L))).comp (algebraMap R κ) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgFin R F j) q) :
      ↥(chartAlgFin R F j) ⊗[R] κ) = (1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] (algebraMap R κ q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θFin_right (algebraMap R κ q)
  show D.θFin (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgFin R F j) q)) =
    algebraMap κ ↥(chartRing κ ({t} : Set L)) (algebraMap R κ q)
  rw [h1, ← h2]
  rfl

theorem ρInf_comp_algebraMap :
    D.ρInf.comp (algebraMap R ↥(chartAlgInf R F j)) =
      (algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L))).comp (algebraMap R κ) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgInf R F j) q) :
      ↥(chartAlgInf R F j) ⊗[R] κ) = (1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] (algebraMap R κ q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θInf_right (algebraMap R κ q)
  show D.θInf (Algebra.TensorProduct.includeLeftRingHom (algebraMap R ↥(chartAlgInf R F j) q)) =
    algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L)) (algebraMap R κ q)
  rw [h1, ← h2]
  rfl

abbrev uFin : X₀ κ t ⟶ XFin R F j := Spec.map (CommRingCat.ofHom D.ρFin)

abbrev uInf : CurveModel.XInf κ t ⟶ TwoChartIntegralModel.XInf R F j := Spec.map (CommRingCat.ofHom D.ρInf)

abbrev uMid : XOverlap κ t ⟶ XMid R F j := Spec.map (CommRingCat.ofHom D.ρMid)

theorem f₀_uFin : f₀ κ t ≫ uFin D = uMid D ≫ fFin R F j := by
  simp only [f₀, uFin, uMid, fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_fin

theorem fInf_uInf : CurveModel.fInf κ t ≫ uInf D = uMid D ≫ TwoChartIntegralModel.fInf R F j := by
  simp only [CurveModel.fInf, uInf, uMid, TwoChartIntegralModel.fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_inf

theorem glue_compat :
    f₀ κ t ≫ (uFin D ≫ ιFin R F j) = CurveModel.fInf κ t ≫ (uInf D ≫ TwoChartIntegralModel.ιInf R F j) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    TwoChartIntegralModel.glue_condition]

def u : glued κ t ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  pushout.desc (uFin D ≫ ιFin R F j) (uInf D ≫ TwoChartIntegralModel.ιInf R F j) (glue_compat D)

@[reassoc]
theorem ι₀_u : ι₀ κ t ≫ u D = uFin D ≫ ιFin R F j := pushout.inl_desc _ _ _

@[reassoc]
theorem ιInf_u : CurveModel.ιInf κ t ≫ u D = uInf D ≫ TwoChartIntegralModel.ιInf R F j := pushout.inr_desc _ _ _

theorem uFin_base :
    uFin D ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))) =
      Spec.map (CommRingCat.ofHom (algebraMap κ ↥(chartRing κ ({t} : Set L)))) ≫ baseMap R κ := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρFin_comp_algebraMap D)

theorem uInf_base :
    uInf D ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j))) =
      Spec.map (CommRingCat.ofHom (algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L)))) ≫ baseMap R κ := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρInf_comp_algebraMap D)

theorem u_toBase : u D ≫ toBase R F j = gluedToBase κ t ≫ baseMap R κ := by
  refine pushout.hom_ext (f := f₀ κ t) (g := CurveModel.fInf κ t) ?_ ?_
  · change ι₀ κ t ≫ u D ≫ toBase R F j = ι₀ κ t ≫ gluedToBase κ t ≫ baseMap R κ
    rw [ι₀_u_assoc, ιFin_toBase, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf κ t ≫ u D ≫ toBase R F j = CurveModel.ιInf κ t ≫ gluedToBase κ t ≫ baseMap R κ
    rw [ιInf_u_assoc, ιInf_toBase, uInf_base, ιInf_gluedToBase_assoc]

def es : glued κ t ⟶ pullback (toBase R F j) (baseMap R κ) :=
  pullback.lift (u D) (gluedToBase κ t) (u_toBase D)

@[reassoc (attr := simp)]
theorem es_fst : es D ≫ pullback.fst (toBase R F j) (baseMap R κ) = u D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem es_snd : es D ≫ pullback.snd (toBase R F j) (baseMap R κ) = gluedToBase κ t := pullback.lift_snd _ _ _

theorem ι₀_es_fst : ι₀ κ t ≫ es D ≫ pullback.fst (toBase R F j) (baseMap R κ) = uFin D ≫ ιFin R F j := by
  rw [es_fst, ι₀_u]

theorem ιInf_es_fst :
    CurveModel.ιInf κ t ≫ es D ≫ pullback.fst (toBase R F j) (baseMap R κ) =
      uInf D ≫ TwoChartIntegralModel.ιInf R F j := by
  rw [es_fst, ιInf_u]

theorem uInf_asIdeal (z : CurveModel.XInf κ t) : ((uInf D).base z).asIdeal = z.asIdeal.comap D.ρInf := rfl

theorem u_mem_range_ιFin_iff (y : glued κ t) :
    (u D).base y ∈ Set.range (ιFin R F j).base ↔ y ∈ Set.range (ι₀ κ t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf κ t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin D).base x₀, ?_⟩⟩
    change (uFin D ≫ ιFin R F j).base x₀ = (ι₀ κ t ≫ u D).base x₀
    rw [ι₀_u]
  · have hz : (u D).base ((CurveModel.ιInf κ t).base z) =
        (TwoChartIntegralModel.ιInf R F j).base ((uInf D).base z) := by
      change (CurveModel.ιInf κ t ≫ u D).base z = (uInf D ≫ TwoChartIntegralModel.ιInf R F j).base z
      rw [ιInf_u]
    rw [hz, tc_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap]
    have hpin : D.ρInf (jInvChartInf R F j) = tInvChart κ t ^ D.m := D.ρInf_jInv
    rw [hpin]
    exact not_congr (Ideal.IsPrime.pow_mem_iff_mem inferInstance D.m D.m_pos)

theorem uFin_asIdeal (x₀ : X₀ κ t) : ((uFin D).base x₀).asIdeal = x₀.asIdeal.comap D.ρFin := rfl

theorem u_mem_range_ιInf_iff (y : glued κ t) :
    (u D).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔ y ∈ Set.range (CurveModel.ιInf κ t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf κ t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · have hx : (u D).base ((ι₀ κ t).base x₀) = (ιFin R F j).base ((uFin D).base x₀) := by
      change (ι₀ κ t ≫ u D).base x₀ = (uFin D ≫ ιFin R F j).base x₀
      rw [ι₀_u]
    rw [hx, tc_ιFin_mem_range_ιInf_iff, ι₀_mem_range_ιInf_iff, uFin_asIdeal, Ideal.mem_comap]
    have hpin : D.ρFin (jChartFin R F j) = tChart κ t ^ D.m := D.ρFin_j
    rw [hpin]
    exact not_congr (Ideal.IsPrime.pow_mem_iff_mem inferInstance D.m D.m_pos)
  · refine ⟨fun _ => ⟨z, rfl⟩, fun _ => ⟨(uInf D).base z, ?_⟩⟩
    change (uInf D ≫ TwoChartIntegralModel.ιInf R F j).base z = (CurveModel.ιInf κ t ≫ u D).base z
    rw [ιInf_u]

theorem es_fst_mem_range_ιInf_iff (y : glued κ t) :
    (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      y ∈ Set.range (CurveModel.ιInf κ t).base := by
  rw [es_fst]; exact u_mem_range_ιInf_iff D y

theorem es_fst_mem_range_ιFin_iff (y : glued κ t) :
    (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (ιFin R F j).base ↔
      y ∈ Set.range (ι₀ κ t).base := by
  rw [es_fst]; exact u_mem_range_ιFin_iff D y

abbrev PFin (_D : GlueDatum R F j κ t) := pullback (ιFin R F j) (pullback.fst (toBase R F j) (baseMap R κ))

abbrev PInf (_D : GlueDatum R F j κ t) :=
  pullback (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ))

def φFin : X₀ κ t ⟶ PFin D :=
  pullback.lift (uFin D) (ι₀ κ t ≫ es D) (by rw [Category.assoc, ι₀_es_fst])

def φInf : CurveModel.XInf κ t ⟶ PInf D :=
  pullback.lift (uInf D) (CurveModel.ιInf κ t ≫ es D) (by rw [Category.assoc, ιInf_es_fst])

@[reassoc (attr := simp)]
theorem φFin_fst : φFin D ≫ pullback.fst _ _ = uFin D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem φFin_snd : φFin D ≫ pullback.snd _ _ = ι₀ κ t ≫ es D := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem φInf_fst : φInf D ≫ pullback.fst _ _ = uInf D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem φInf_snd : φInf D ≫ pullback.snd _ _ = CurveModel.ιInf κ t ≫ es D := pullback.lift_snd _ _ _

def isoFin : PFin D ≅ Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ)) :=
  pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j) ≪≫
    pullback.congrHom (ιFin_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgFin R F j) κ

def isoInf : PInf D ≅ Spec (CommRingCat.of (↥(chartAlgInf R F j) ⊗[R] κ)) :=
  pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j) ≪≫
    pullback.congrHom (ιInf_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgInf R F j) κ

set_option maxHeartbeats 1600000 in

theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom D.θFin) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).inv =
      φFin D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j)).hom ≫
        (pullback.congrHom (ιFin_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θFin_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, es_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom D.θInf) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv =
      φInf D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
        (pullback.congrHom (ιInf_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θInf_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, es_snd, ιInf_gluedToBase]

theorem φFin_isoFin : φFin D ≫ (isoFin D).hom = Spec.map (CommRingCat.ofHom D.θFin) := by
  calc φFin D ≫ (isoFin D).hom
      = (φFin D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (ιFin R F j)).hom ≫
          (pullback.congrHom (ιFin_toBase R F j) rfl).hom) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom := by
        simp only [isoFin, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom D.θFin) ≫ (pullbackSpecIso R ↥(chartAlgFin R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgFin R F j) κ).hom := by rw [SpecMap_θFin_eq]
    _ = Spec.map (CommRingCat.ofHom D.θFin) := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem φInf_isoInf : φInf D ≫ (isoInf D).hom = Spec.map (CommRingCat.ofHom D.θInf) := by
  calc φInf D ≫ (isoInf D).hom
      = (φInf D ≫ (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
          (pullback.congrHom (ιInf_toBase R F j) rfl).hom) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by
        simp only [isoInf, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom D.θInf) ≫ (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by rw [SpecMap_θInf_eq]
    _ = Spec.map (CommRingCat.ofHom D.θInf) := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

scoped instance isClosedImmersion_φFin : IsClosedImmersion (φFin D) := by
  have h : φFin D = Spec.map (CommRingCat.ofHom D.θFin) ≫ (isoFin D).inv := by
    rw [← φFin_isoFin, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom D.θFin)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom D.θFin) (by simpa using D.surjFin)
  rw [h]
  infer_instance

scoped instance isClosedImmersion_φInf : IsClosedImmersion (φInf D) := by
  have h : φInf D = Spec.map (CommRingCat.ofHom D.θInf) ≫ (isoInf D).inv := by
    rw [← φInf_isoInf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom D.θInf)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom D.θInf) (by simpa using D.surjInf)
  rw [h]
  infer_instance

abbrev gFin : PFin D ⟶ pullback (toBase R F j) (baseMap R κ) := pullback.snd _ _

abbrev gInf : PInf D ⟶ pullback (toBase R F j) (baseMap R κ) := pullback.snd _ _

theorem range_gFin : Set.range (gFin D).base =
    (pullback.fst (toBase R F j) (baseMap R κ)).base ⁻¹' Set.range (ιFin R F j).base := by
  rw [gFin, IsOpenImmersion.range_pullbackSnd]; rfl

theorem range_gInf : Set.range (gInf D).base =
    (pullback.fst (toBase R F j) (baseMap R κ)).base ⁻¹' Set.range (TwoChartIntegralModel.ιInf R F j).base := by
  rw [gInf, IsOpenImmersion.range_pullbackSnd]; rfl

theorem range_pullback_fst_gFin :
    Set.range (pullback.fst (es D) (gFin D)).base = Set.range (ι₀ κ t).base := by
  rw [IsOpenImmersion.range_pullbackFst]
  ext y
  change (es D).base y ∈ Set.range (gFin D).base ↔ _
  rw [range_gFin, Set.mem_preimage]
  exact es_fst_mem_range_ιFin_iff D y

theorem range_pullback_fst_gInf :
    Set.range (pullback.fst (es D) (gInf D)).base = Set.range (CurveModel.ιInf κ t).base := by
  rw [IsOpenImmersion.range_pullbackFst]
  ext y
  change (es D).base y ∈ Set.range (gInf D).base ↔ _
  rw [range_gInf, Set.mem_preimage]
  exact es_fst_mem_range_ιInf_iff D y

theorem isClosedImmersion_pullback_snd_gFin : IsClosedImmersion (pullback.snd (es D) (gFin D)) := by
  let e := IsOpenImmersion.isoOfRangeEq (ι₀ κ t) (pullback.fst (es D) (gFin D)) (range_pullback_fst_gFin D).symm
  have he : e.hom ≫ pullback.fst (es D) (gFin D) = ι₀ κ t := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h : e.hom ≫ pullback.snd (es D) (gFin D) = φFin D := by
    rw [← cancel_mono (gFin D)]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he, φFin_snd]
  have h' : pullback.snd (es D) (gFin D) = e.inv ≫ φFin D := by rw [← h, Iso.inv_hom_id_assoc]
  rw [h']
  infer_instance

theorem isClosedImmersion_pullback_snd_gInf : IsClosedImmersion (pullback.snd (es D) (gInf D)) := by
  let e := IsOpenImmersion.isoOfRangeEq (CurveModel.ιInf κ t) (pullback.fst (es D) (gInf D)) (range_pullback_fst_gInf D).symm
  have he : e.hom ≫ pullback.fst (es D) (gInf D) = CurveModel.ιInf κ t := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h : e.hom ≫ pullback.snd (es D) (gInf D) = φInf D := by
    rw [← cancel_mono (gInf D)]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he, φInf_snd]
  have h' : pullback.snd (es D) (gInf D) = e.inv ≫ φInf D := by rw [← h, Iso.inv_hom_id_assoc]
  rw [h']
  infer_instance

def fibreCover : (pullback (toBase R F j) (baseMap R κ)).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => cond b (PFin D) (PInf D))
    (fun b => match b with
      | true => gFin D
      | false => gInf D)
    (by
      intro x
      rcases mem_range_ιFin_or_mem_range_ιInf R F j ((pullback.fst (toBase R F j) (baseMap R κ)).base x) with hx | hx
      · have hx' : x ∈ Set.range (gFin D).base := by rw [range_gFin]; exact hx
        obtain ⟨y, hy⟩ := hx'
        exact ⟨true, y, hy⟩
      · have hx' : x ∈ Set.range (gInf D).base := by rw [range_gInf]; exact hx
        obtain ⟨y, hy⟩ := hx'
        exact ⟨false, y, hy⟩)
    (fun b => match b with
      | true => (inferInstance : IsOpenImmersion (gFin D))
      | false => (inferInstance : IsOpenImmersion (gInf D)))

theorem isClosedImmersion_es : IsClosedImmersion (es D) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (fibreCover D) ?_
  intro b
  match b with
  | true => exact isClosedImmersion_pullback_snd_gFin D
  | false => exact isClosedImmersion_pullback_snd_gInf D

theorem gFin_mem_range_es_iff (z : PFin D) :
    (gFin D).base z ∈ Set.range (es D).base ↔ z ∈ Set.range (φFin D).base := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈ Set.range (ιFin R F j).base := by
      refine ⟨(pullback.fst (ιFin R F j) _).base z, ?_⟩
      change _ = ((es D).base ≫ (pullback.fst (toBase R F j) (baseMap R κ)).base) y
      rw [TopCat.comp_app, hy]
      change (pullback.fst (ιFin R F j) _ ≫ ιFin R F j).base z = (gFin D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base z
      rw [pullback.condition]
    obtain ⟨x₀, rfl⟩ := (es_fst_mem_range_ιFin_iff D y).mp hy'
    refine ⟨x₀, (gFin D).isOpenEmbedding.injective ?_⟩
    change ((φFin D) ≫ gFin D).base x₀ = _
    rw [φFin_snd]
    exact hy
  · rintro ⟨x₀, rfl⟩
    refine ⟨(ι₀ κ t).base x₀, ?_⟩
    change (ι₀ κ t ≫ es D).base x₀ = (φFin D ≫ gFin D).base x₀
    rw [φFin_snd]

theorem gInf_mem_range_es_iff (z : PInf D) :
    (gInf D).base z ∈ Set.range (es D).base ↔ z ∈ Set.range (φInf D).base := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (es D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base y ∈
        Set.range (TwoChartIntegralModel.ιInf R F j).base := by
      refine ⟨(pullback.fst (TwoChartIntegralModel.ιInf R F j) _).base z, ?_⟩
      change _ = ((es D).base ≫ (pullback.fst (toBase R F j) (baseMap R κ)).base) y
      rw [TopCat.comp_app, hy]
      change (pullback.fst (TwoChartIntegralModel.ιInf R F j) _ ≫ TwoChartIntegralModel.ιInf R F j).base z =
        (gInf D ≫ pullback.fst (toBase R F j) (baseMap R κ)).base z
      rw [pullback.condition]
    obtain ⟨xi, rfl⟩ := (es_fst_mem_range_ιInf_iff D y).mp hy'
    refine ⟨xi, (gInf D).isOpenEmbedding.injective ?_⟩
    change ((φInf D) ≫ gInf D).base xi = _
    rw [φInf_snd]
    exact hy
  · rintro ⟨xi, rfl⟩
    refine ⟨(CurveModel.ιInf κ t).base xi, ?_⟩
    change (CurveModel.ιInf κ t ≫ es D).base xi = (φInf D ≫ gInf D).base xi
    rw [φInf_snd]

theorem mem_range_φFin_iff (z : PFin D) :
    z ∈ Set.range (φFin D).base ↔ RingHom.ker D.θFin ≤ ((isoFin D).hom.base z).asIdeal := by
  have hbij := (isoFin D).hom.homeomorph.injective
  constructor
  · rintro ⟨x₀, rfl⟩
    have : (isoFin D).hom.base ((φFin D).base x₀) = (Spec.map (CommRingCat.ofHom D.θFin)).base x₀ := by
      change (φFin D ≫ (isoFin D).hom).base x₀ = _
      rw [φFin_isoFin]
    rw [this]
    change RingHom.ker D.θFin ≤ (x₀.asIdeal.comap D.θFin)
    exact fun a ha => by simp [Ideal.mem_comap, RingHom.mem_ker.mp ha]
  · intro h
    have hz : (isoFin D).hom.base z ∈ Set.range (Spec.map (CommRingCat.ofHom D.θFin)).base := by
      change (isoFin D).hom.base z ∈ Set.range (PrimeSpectrum.comap D.θFin)
      rw [range_comap_of_surjective _ D.θFin D.surjFin]
      exact h
    obtain ⟨x₀, hx₀⟩ := hz
    refine ⟨x₀, hbij ?_⟩
    change ((φFin D) ≫ (isoFin D).hom).base x₀ = _
    rw [φFin_isoFin]
    exact hx₀

theorem mem_range_φInf_iff (z : PInf D) :
    z ∈ Set.range (φInf D).base ↔ RingHom.ker D.θInf ≤ ((isoInf D).hom.base z).asIdeal := by
  have hbij := (isoInf D).hom.homeomorph.injective
  constructor
  · rintro ⟨xi, rfl⟩
    have : (isoInf D).hom.base ((φInf D).base xi) = (Spec.map (CommRingCat.ofHom D.θInf)).base xi := by
      change (φInf D ≫ (isoInf D).hom).base xi = _
      rw [φInf_isoInf]
    rw [this]
    change RingHom.ker D.θInf ≤ (xi.asIdeal.comap D.θInf)
    exact fun a ha => by simp [Ideal.mem_comap, RingHom.mem_ker.mp ha]
  · intro h
    have hz : (isoInf D).hom.base z ∈ Set.range (Spec.map (CommRingCat.ofHom D.θInf)).base := by
      change (isoInf D).hom.base z ∈ Set.range (PrimeSpectrum.comap D.θInf)
      rw [range_comap_of_surjective _ D.θInf D.surjInf]
      exact h
    obtain ⟨xi, hxi⟩ := hz
    refine ⟨xi, hbij ?_⟩
    change ((φInf D) ≫ (isoInf D).hom).base xi = _
    rw [φInf_isoInf]
    exact hxi

end Schemes

section Datum

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L}

variable
  (eFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(chartRing κ ({t} : Set L)))
  (eInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(chartRing κ ({t⁻¹} : Set L)))

def θF : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(chartRing κ ({t} : Set L)) :=
  (eFin : κ ⊗[R] ↥(chartAlgFin R F j) →+* ↥(chartRing κ ({t} : Set L))).comp
    (RingHomClass.toRingHom (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ))

def θI : ↥(chartAlgInf R F j) ⊗[R] κ →+* ↥(chartRing κ ({t⁻¹} : Set L)) :=
  (eInf : κ ⊗[R] ↥(chartAlgInf R F j) →+* ↥(chartRing κ ({t⁻¹} : Set L))).comp
    (RingHomClass.toRingHom (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ))

theorem θF_tmul (b : ↥(chartAlgFin R F j)) (x : κ) : θF eFin (b ⊗ₜ[R] x) = eFin (x ⊗ₜ[R] b) := by
  show eFin (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

theorem θI_tmul (b : ↥(chartAlgInf R F j)) (x : κ) : θI eInf (b ⊗ₜ[R] x) = eInf (x ⊗ₜ[R] b) := by
  show eInf (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

theorem θF_right :
    (θF eFin).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgFin R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θF eFin ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] x) = _
  rw [θF_tmul]
  have hx : (x ⊗ₜ[R] (1 : ↥(chartAlgFin R F j)) : κ ⊗[R] ↥(chartAlgFin R F j)) = algebraMap κ _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgHom.commutes]

theorem θI_right :
    (θI eInf).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      κ →ₐ[R] ↥(chartAlgInf R F j) ⊗[R] κ)) = algebraMap κ ↥(chartRing κ ({t⁻¹} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θI eInf ((1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] x) = _
  rw [θI_tmul]
  have hx : (x ⊗ₜ[R] (1 : ↥(chartAlgInf R F j)) : κ ⊗[R] ↥(chartAlgInf R F j)) = algebraMap κ _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgHom.commutes]

theorem θF_includeLeft (b : ↥(chartAlgFin R F j)) :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b = eFin ((1 : κ) ⊗ₜ[R] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θF_tmul]

theorem θI_includeLeft (b : ↥(chartAlgInf R F j)) :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b = eInf ((1 : κ) ⊗ₜ[R] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θI_tmul]

def gMid : ↥(chartAlgFin R F j) →+* ↥(chartRing κ ({t, t⁻¹} : Set L)) :=
  (incl₀ κ t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom)

theorem coe_gMid (b : ↥(chartAlgFin R F j)) : (gMid (t := t) eFin b : L) = (eFin ((1 : κ) ⊗ₜ[R] b) : L) := by
  show ((incl₀ κ t) ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b) : L) = _
  rw [CurveModel.coe_chartIncl, θF_includeLeft]

variable {m : ℕ}

theorem isUnit_gMid_j [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) :
    IsUnit (gMid (t := t) eFin (jChartFin R F j)) := by
  have h : gMid (t := t) eFin (jChartFin R F j) = incl₀ κ t (tChart κ t) ^ m := by
    apply Subtype.ext
    rw [coe_gMid, hj, Subalgebra.coe_pow, CurveModel.coe_chartIncl, coe_tChart]
  rw [h]
  exact (isUnit_incl₀_tChart κ t Fact.out).pow m

def ρM [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) :
    ↥(chartAlgMid R F j) →+* ↥(chartRing κ ({t, t⁻¹} : Set L)) :=
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  IsLocalization.Away.lift (jChartFin R F j) (g := gMid (t := t) eFin) (isUnit_gMid_j eFin hj)

theorem ρM_inclFin [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) (b : ↥(chartAlgFin R F j)) :
    ρM eFin hj (TwoChartIntegralModel.inclFin R F j b) = gMid (t := t) eFin b := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact IsLocalization.Away.lift_eq (jChartFin R F j) (isUnit_gMid_j eFin hj) b

private theorem _root_.GLUECI.sq_fin [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m) :
    (incl₀ κ t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (TwoChartIntegralModel.inclFin R F j).toRingHom :=
  RingHom.ext fun b => (ρM_inclFin eFin hj b).symm

p2m_export "GLUECI" "sq_fin"

private theorem _root_.GLUECI.sq_inf [Fact (t ≠ 0)] (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n → ((eFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((eInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n)) :
    (CurveModel.inclInf κ t).toRingHom.comp ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (TwoChartIntegralModel.inclInf R F j).toRingHom := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  refine RingHom.ext fun b' => Subtype.ext ?_
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Submonoid.powers (jChartFin R F j)) (TwoChartIntegralModel.inclInf R F j b')
  have h' : (TwoChartIntegralModel.inclInf R F j b') * (TwoChartIntegralModel.inclFin R F j (jChartFin R F j)) ^ n =
      TwoChartIntegralModel.inclFin R F j b := by
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    exact h
  have hF : (b : F) = (b' : F) * j ^ n := by
    have := congrArg (fun z : ↥(chartAlgMid R F j) => (z : F)) h'
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, TwoChartIntegralModel.coe_chartIncl, coe_jChartFin]
      using this.symm
  have hc := hcompat b b' n hF
  have hρ := congrArg (fun z : ↥(chartAlgMid R F j) => ((ρM eFin hj z : ↥(chartRing κ ({t, t⁻¹} : Set L))) : L)) h'
  simp only [map_mul, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow] at hρ
  rw [ρM_inclFin, ρM_inclFin, coe_gMid, coe_gMid, hj, hc, ← pow_mul] at hρ
  have htn : t ^ (m * n) ≠ 0 := pow_ne_zero _ Fact.out
  have hmain : ((ρM eFin hj (TwoChartIntegralModel.inclInf R F j b') : ↥(chartRing κ ({t, t⁻¹} : Set L))) : L) =
      (eInf ((1 : κ) ⊗ₜ[R] b') : L) :=
    mul_right_cancel₀ htn hρ
  show ((CurveModel.inclInf κ t) ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b') : L) =
    ((ρM eFin hj (TwoChartIntegralModel.inclInf R F j b') : ↥(chartRing κ ({t, t⁻¹} : Set L))) : L)
  rw [CurveModel.coe_chartIncl, θI_includeLeft, hmain]

p2m_export "GLUECI" "sq_inf"

private def _root_.GLUECI.datum [Fact (t ≠ 0)] (hm : 0 < m) (hj : ((eFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hcompat : ∀ (b : ↥(chartAlgFin R F j)) (b' : ↥(chartAlgInf R F j)) (n : ℕ),
      (b : F) = (b' : F) * j ^ n → ((eFin ((1 : κ) ⊗ₜ[R] b)) : L) = ((eInf ((1 : κ) ⊗ₜ[R] b')) : L) * t ^ (m * n))
    (hjInv : ((eInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (hFin : Function.Surjective eFin) (hInf : Function.Surjective eInf) : GlueDatum R F j κ t where
  θFin := θF eFin
  θInf := θI eInf
  ρMid := ρM eFin hj
  θFin_right := θF_right eFin
  θInf_right := θI_right eInf
  sq_fin := sq_fin eFin hj
  sq_inf := sq_inf eFin eInf hj hcompat
  m := m
  m_pos := hm
  ρFin_j := Subtype.ext (by rw [θF_includeLeft, hj, Subalgebra.coe_pow, coe_tChart])
  ρInf_jInv := Subtype.ext (by rw [θI_includeLeft, hjInv, Subalgebra.coe_pow, coe_tInvChart])
  surjFin := hFin.comp (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).surjective
  surjInf := hInf.comp (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).surjective

p2m_export "GLUECI" "datum"
theorem ρFin_eq :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom =
      eFin.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom :=
  RingHom.ext fun b => θF_includeLeft eFin b

theorem ρInf_eq :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom =
      eInf.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom :=
  RingHom.ext fun b => θI_includeLeft eInf b

theorem ker_θF : RingHom.ker (θF eFin) =
    RingHom.ker (eFin.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) := rfl

theorem ker_θI : RingHom.ker (θI eInf) =
    RingHom.ker (eInf.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgInf R F j) κ).toRingHom) := rfl

end Datum

end GLUECI
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel"

open scoped TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.range_pullbackFst pullbackSpecIso_inv_snd Surjective Spec.map_comp_assoc Scheme.Hom affine_isReduced_iff Scheme.Pullback.range_map Scheme.IsLocallyDirected.ι_eq_ι_iff isIso_iff_isOpenImmersion_and_epi_base IsZariskiLocalAtTarget Spec IsIntegral Spec.map Scheme pullbackSpecIso IsOpenImmersion.range_pullbackSnd pullbackSpecIso_inv_fst_assoc IsOpenImmersion Scheme.Hom.appIso_inv_app_apply Scheme.Pullback.openCoverOfBase Scheme.Hom.comp_base IsReduced.of_openCover pullbackSpecIso_inv_fst IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced Spec.stalkIso IsOpenImmersion.isoOfRangeEq Spec.map_id Scheme.Cover.mkOfCovers IsZariskiLocalAtTarget.of_openCover pullbackSpecIso_hom_fst Spec.germ_stalkMapIso_hom Scheme.Hom.germ_stalkMap isReduced_of_isOpenImmersion Scheme.Hom.comp_apply Scheme.Cover IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

namespace Spec p2m_export "AlgebraicGeometry.Spec" "map_comp map_comp_assoc map map_injective preimage stalkIso map_id germ_stalkMapIso_hom full" end Spec
p2m_open_scoped "AlgebraicGeometry.Spec" in

def Spec.isoOfRingEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Spec (CommRingCat.of R) ≅ Spec (CommRingCat.of S) where
  hom := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp

p2m_open_scoped "AlgebraicGeometry.Spec" in
@[scoped simp]
theorem Spec.isoOfRingEquiv_hom {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (Spec.isoOfRingEquiv e).hom = Spec.map (CommRingCat.ofHom e.symm.toRingHom) := rfl

p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec"
p2m_open_scoped "AlgebraicGeometry.Spec" in
@[scoped simp]
theorem Spec.isoOfRingEquiv_inv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (Spec.isoOfRingEquiv e).inv = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec"

variable {B : Type u} [CommRing B] (I₁ I₂ : Ideal B)

def quotTensorQuotEquivQuotSup : (B ⧸ I₁) ⊗[B] (B ⧸ I₂) ≃+* B ⧸ (I₁ ⊔ I₂) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (B ⧸ I₁) I₂).symm.toRingEquiv.trans
    (DoubleQuot.quotQuotEquivQuotSup I₁ I₂)

theorem mk_tmul_mk_eq_mk_mul_tmul_one (a b : B) :
    (Ideal.Quotient.mk I₁ a ⊗ₜ[B] Ideal.Quotient.mk I₂ b : (B ⧸ I₁) ⊗[B] (B ⧸ I₂)) =
      Ideal.Quotient.mk I₁ (a * b) ⊗ₜ[B] 1 := by
  have h2 : Ideal.Quotient.mk I₂ b = b • (1 : B ⧸ I₂) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have h1 : Ideal.Quotient.mk I₁ (a * b) = b • Ideal.Quotient.mk I₁ a := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm]
  rw [h2, TensorProduct.tmul_smul, h1, TensorProduct.smul_tmul']

@[scoped simp]
theorem quotTensorQuotEquivQuotSup_symm_mk (b : B) :
    (quotTensorQuotEquivQuotSup I₁ I₂).symm (Ideal.Quotient.mk (I₁ ⊔ I₂) b) =
      Ideal.Quotient.mk I₁ b ⊗ₜ[B] 1 := by
  simp only [quotTensorQuotEquivQuotSup, RingEquiv.symm_trans_apply]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk (B ⧸ I₁) I₂ (Ideal.Quotient.mk I₁ b)

@[scoped simp]
theorem quotTensorQuotEquivQuotSup_tmul (a b : B) :
    quotTensorQuotEquivQuotSup I₁ I₂ (Ideal.Quotient.mk I₁ a ⊗ₜ[B] Ideal.Quotient.mk I₂ b) =
      Ideal.Quotient.mk (I₁ ⊔ I₂) (a * b) := by
  apply (quotTensorQuotEquivQuotSup I₁ I₂).symm.injective
  rw [RingEquiv.symm_apply_apply, quotTensorQuotEquivQuotSup_symm_mk,
    mk_tmul_mk_eq_mk_mul_tmul_one]

theorem quotTensorQuotEquivQuotSup_comp_includeLeftRingHom :
    (quotTensorQuotEquivQuotSup I₁ I₂).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
  simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    Ideal.Quotient.factor_mk, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← map_one (Ideal.Quotient.mk I₂), quotTensorQuotEquivQuotSup_tmul, mul_one]

theorem quotTensorQuotEquivQuotSup_comp_includeRight :
    (quotTensorQuotEquivQuotSup I₁ I₂).toRingHom.comp
        ((Algebra.TensorProduct.includeRight : (B ⧸ I₂) →ₐ[B] (B ⧸ I₁) ⊗[B] (B ⧸ I₂)) :
          (B ⧸ I₂) →+* (B ⧸ I₁) ⊗[B] (B ⧸ I₂)) =
      Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
  simp only [RingHom.comp_apply, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Ideal.Quotient.factor_mk, RingEquiv.toRingHom_eq_coe]
  rw [← map_one (Ideal.Quotient.mk I₁), quotTensorQuotEquivQuotSup_tmul, one_mul]

theorem pullbackSpecIso_quot_inv_fst :
    (pullbackSpecIso B (B ⧸ I₁) (B ⧸ I₂)).inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₁)))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₂))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : (B ⧸ I₁) →+* (B ⧸ I₁) ⊗[B] (B ⧸ I₂))) :=
  pullbackSpecIso_inv_fst B (B ⧸ I₁) (B ⧸ I₂)

theorem pullbackSpecIso_quot_inv_snd :
    (pullbackSpecIso B (B ⧸ I₁) (B ⧸ I₂)).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₁)))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₂))) =
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : (B ⧸ I₂) →ₐ[B] (B ⧸ I₁) ⊗[B] (B ⧸ I₂)) :
          (B ⧸ I₂) →+* (B ⧸ I₁) ⊗[B] (B ⧸ I₂))) :=
  pullbackSpecIso_inv_snd B (B ⧸ I₁) (B ⧸ I₂)

def specQuotPullbackIso :
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₁)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₂))) ≅
      Spec (CommRingCat.of (B ⧸ (I₁ ⊔ I₂))) :=
  pullbackSpecIso B (B ⧸ I₁) (B ⧸ I₂) ≪≫ Spec.isoOfRingEquiv (quotTensorQuotEquivQuotSup I₁ I₂)

@[reassoc]
theorem specQuotPullbackIso_inv_fst :
    (specQuotPullbackIso I₁ I₂).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂))) := by
  simp only [specQuotPullbackIso, Iso.trans_inv, Spec.isoOfRingEquiv_inv, Category.assoc,
    pullbackSpecIso_quot_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotTensorQuotEquivQuotSup_comp_includeLeftRingHom]

@[reassoc]
theorem specQuotPullbackIso_inv_snd :
    (specQuotPullbackIso I₁ I₂).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂))) := by
  simp only [specQuotPullbackIso, Iso.trans_inv, Spec.isoOfRingEquiv_inv, Category.assoc,
    pullbackSpecIso_quot_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotTensorQuotEquivQuotSup_comp_includeRight]

@[reassoc]
theorem specQuotPullbackIso_hom_factor_left :
    (specQuotPullbackIso I₁ I₂).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂))) =
      pullback.fst _ _ := by
  rw [← specQuotPullbackIso_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc]
theorem specQuotPullbackIso_hom_factor_right :
    (specQuotPullbackIso I₁ I₂).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂))) =
      pullback.snd _ _ := by
  rw [← specQuotPullbackIso_inv_snd, Iso.hom_inv_id_assoc]

@[reassoc]
theorem specQuotPullbackIso_inv_fst_mk :
    (specQuotPullbackIso I₁ I₂).inv ≫ pullback.fst _ _ ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₁)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I₁ ⊔ I₂))) := by
  rw [specQuotPullbackIso_inv_fst_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

theorem isReduced_pullback_spec_quotient_iff :
    IsReduced (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₁)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₂)))) ↔
      _root_.IsReduced (B ⧸ (I₁ ⊔ I₂)) := by
  have h : IsReduced (Spec (CommRingCat.of (B ⧸ (I₁ ⊔ I₂)))) ↔ _root_.IsReduced (B ⧸ (I₁ ⊔ I₂)) :=
    affine_isReduced_iff _
  rw [← h]
  exact ⟨fun _ => isReduced_of_isOpenImmersion (specQuotPullbackIso I₁ I₂).inv,
    fun _ => isReduced_of_isOpenImmersion (specQuotPullbackIso I₁ I₂).hom⟩

theorem natCard_pullback_spec_quotient :
    Nat.card ↥(pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₁)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I₂)))) =
      Nat.card (PrimeSpectrum (B ⧸ (I₁ ⊔ I₂))) :=
  Nat.card_congr (specQuotPullbackIso I₁ I₂).schemeIsoToHomeo.toEquiv

theorem ker_isPrime_of_isDomain {R C : Type*} [CommRing R] [CommRing C] [IsDomain C]
    (f : R →+* C) : (RingHom.ker f).IsPrime :=
  RingHom.ker_isPrime f

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

namespace GLUECI

open AlgebraicCurve.TwoChartIntegralModel

abbrev specQuotMk {B : Type u} [CommRing B] (I : Ideal B) :
    Spec (CommRingCat.of (B ⧸ I)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

section Pair

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

section One

variable (D : GlueDatum R F j κ t)

def GlueDatum.IFin : Ideal (↥(chartAlgFin R F j) ⊗[R] κ) := RingHom.ker D.θFin

def GlueDatum.IInf : Ideal (↥(chartAlgInf R F j) ⊗[R] κ) := RingHom.ker D.θInf

omit [Fact (t ≠ 0)] in
theorem GlueDatum.IFin_eq : D.IFin = RingHom.ker D.θFin := rfl

omit [Fact (t ≠ 0)] in
theorem GlueDatum.IInf_eq : D.IInf = RingHom.ker D.θInf := rfl

def eFin : X₀ κ t ≅ pullback (es D) (gFin D) :=
  IsOpenImmersion.isoOfRangeEq (ι₀ κ t) (pullback.fst (es D) (gFin D))
    (range_pullback_fst_gFin D).symm

def eInf : CurveModel.XInf κ t ≅ pullback (es D) (gInf D) :=
  IsOpenImmersion.isoOfRangeEq (CurveModel.ιInf κ t) (pullback.fst (es D) (gInf D))
    (range_pullback_fst_gInf D).symm

@[reassoc (attr := simp)]
theorem eFin_hom_fst : (eFin D).hom ≫ pullback.fst (es D) (gFin D) = ι₀ κ t :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem eInf_hom_fst : (eInf D).hom ≫ pullback.fst (es D) (gInf D) = CurveModel.ιInf κ t :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc]
theorem eFin_hom_snd : (eFin D).hom ≫ pullback.snd (es D) (gFin D) = φFin D := by
  rw [← cancel_mono (gFin D), Category.assoc, ← pullback.condition, eFin_hom_fst_assoc, φFin_snd]

@[reassoc]
theorem eInf_hom_snd : (eInf D).hom ≫ pullback.snd (es D) (gInf D) = φInf D := by
  rw [← cancel_mono (gInf D), Category.assoc, ← pullback.condition, eInf_hom_fst_assoc, φInf_snd]

theorem pullback_snd_es_gFin : pullback.snd (es D) (gFin D) = (eFin D).inv ≫ φFin D := by
  rw [← eFin_hom_snd, Iso.inv_hom_id_assoc]

theorem pullback_snd_es_gInf : pullback.snd (es D) (gInf D) = (eInf D).inv ≫ φInf D := by
  rw [← eInf_hom_snd, Iso.inv_hom_id_assoc]

omit [Fact (t ≠ 0)] in

theorem quotientKerEquiv_comp_mk_θFin :
    (RingHom.quotientKerEquivOfSurjective D.surjFin).toRingHom.comp
        (Ideal.Quotient.mk D.IFin) = D.θFin :=
  RingHom.ext fun x => RingHom.quotientKerEquivOfSurjective_apply_mk D.surjFin x

omit [Fact (t ≠ 0)] in
theorem quotientKerEquiv_comp_mk_θInf :
    (RingHom.quotientKerEquivOfSurjective D.surjInf).toRingHom.comp
        (Ideal.Quotient.mk D.IInf) = D.θInf :=
  RingHom.ext fun x => RingHom.quotientKerEquivOfSurjective_apply_mk D.surjInf x

def legFin : pullback (es D) (gFin D) ⟶
    Spec (CommRingCat.of ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ D.IFin)) :=
  (eFin D).inv ≫ (Spec.isoOfRingEquiv (RingHom.quotientKerEquivOfSurjective D.surjFin)).inv

def legInf : pullback (es D) (gInf D) ⟶
    Spec (CommRingCat.of ((↥(chartAlgInf R F j) ⊗[R] κ) ⧸ D.IInf)) :=
  (eInf D).inv ≫ (Spec.isoOfRingEquiv (RingHom.quotientKerEquivOfSurjective D.surjInf)).inv

scoped instance isIso_legFin : IsIso (legFin D) := by unfold legFin; infer_instance

scoped instance isIso_legInf : IsIso (legInf D) := by unfold legInf; infer_instance

theorem pullback_snd_isoFin_hom :
    pullback.snd (es D) (gFin D) ≫ (isoFin D).hom =
      legFin D ≫ specQuotMk D.IFin := by
  rw [pullback_snd_es_gFin, Category.assoc, φFin_isoFin, legFin, Category.assoc,
    Spec.isoOfRingEquiv_inv, specQuotMk, ← Spec.map_comp]
  rfl

theorem pullback_snd_isoInf_hom :
    pullback.snd (es D) (gInf D) ≫ (isoInf D).hom =
      legInf D ≫ specQuotMk D.IInf := by
  rw [pullback_snd_es_gInf, Category.assoc, φInf_isoInf, legInf, Category.assoc,
    Spec.isoOfRingEquiv_inv, specQuotMk, ← Spec.map_comp]
  rfl

omit [Fact (t ≠ 0)] in

@[reassoc]
theorem isoInf_hom_SpecMap_includeLeft :
    (isoInf D).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ)) =
      pullback.fst (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ)) := by
  simp only [isoInf, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]

omit [Fact (t ≠ 0)] in

@[reassoc]
theorem isoFin_hom_SpecMap_includeLeft :
    (isoFin D).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ)) =
      pullback.fst (ιFin R F j) (pullback.fst (toBase R F j) (baseMap R κ)) := by
  simp only [isoFin, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]

end One
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

variable (D₁ D₂ : GlueDatum R F j κ t)

omit [Fact (t ≠ 0)] in
theorem isoFin_irrel : isoFin D₁ = isoFin D₂ := rfl

omit [Fact (t ≠ 0)] in
theorem isoInf_irrel : isoInf D₁ = isoInf D₂ := rfl

def finCompare :
    pullback (pullback.snd (es D₁) (gFin D₁)) (pullback.snd (es D₂) (gFin D₂)) ⟶
      pullback (specQuotMk D₁.IFin) (specQuotMk D₂.IFin) :=
  pullback.map _ _ _ _ (legFin D₁) (legFin D₂) (isoFin D₁).hom
    (pullback_snd_isoFin_hom D₁) (pullback_snd_isoFin_hom D₂)

def infCompare :
    pullback (pullback.snd (es D₁) (gInf D₁)) (pullback.snd (es D₂) (gInf D₂)) ⟶
      pullback (specQuotMk D₁.IInf) (specQuotMk D₂.IInf) :=
  pullback.map _ _ _ _ (legInf D₁) (legInf D₂) (isoInf D₁).hom
    (pullback_snd_isoInf_hom D₁) (pullback_snd_isoInf_hom D₂)

scoped instance isIso_finCompare : IsIso (finCompare D₁ D₂) := by unfold finCompare; infer_instance

scoped instance isIso_infCompare : IsIso (infCompare D₁ D₂) := by unfold infCompare; infer_instance

def pairCover : (pullback (es D₁) (es D₂)).OpenCover :=
  Scheme.Pullback.openCoverOfBase (fibreCover D₁) (es D₁) (es D₂)

theorem isReduced_pullback_es
    (hFin : _root_.IsReduced
      ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ (D₁.IFin ⊔ D₂.IFin)))
    (hInf : _root_.IsReduced
      ((↥(chartAlgInf R F j) ⊗[R] κ) ⧸ (D₁.IInf ⊔ D₂.IInf))) :
    IsReduced (pullback (es D₁) (es D₂)) := by
  haveI : ∀ i, IsReduced ((pairCover D₁ D₂).X i) := by
    rintro (_ | _)
    · change IsReduced (pullback (pullback.snd (es D₁) (gInf D₁)) (pullback.snd (es D₂) (gInf D₂)))
      haveI := (isReduced_pullback_spec_quotient_iff
        D₁.IInf D₂.IInf).mpr hInf
      exact isReduced_of_isOpenImmersion (infCompare D₁ D₂)
    · change IsReduced (pullback (pullback.snd (es D₁) (gFin D₁)) (pullback.snd (es D₂) (gFin D₂)))
      haveI := (isReduced_pullback_spec_quotient_iff
        D₁.IFin D₂.IFin).mpr hFin
      exact isReduced_of_isOpenImmersion (finCompare D₁ D₂)
  exact IsReduced.of_openCover _ (pairCover D₁ D₂)

theorem ker_sup_ker_le_of_mem_range (w : PInf D₁)
    (h₁ : (gInf D₁).base w ∈ Set.range (es D₁).base) (h₂ : (gInf D₁).base w ∈ Set.range (es D₂).base) :
    D₁.IInf ⊔ D₂.IInf ≤ ((isoInf D₁).hom.base w).asIdeal := by
  refine sup_le ?_ ?_
  · exact (mem_range_φInf_iff D₁ w).mp ((gInf_mem_range_es_iff D₁ w).mp h₁)
  · exact (mem_range_φInf_iff D₂ w).mp ((gInf_mem_range_es_iff D₂ w).mp h₂)

theorem fst_mem_range_ι₀
    (hmid : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ⊔ D₂.IInf ≤ 𝔮.asIdeal →
        (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) ∉ 𝔮.asIdeal)
    (p : ↥(pullback (es D₁) (es D₂))) :
    (pullback.fst (es D₁) (es D₂)).base p ∈ Set.range (ι₀ κ t).base := by
  rw [← es_fst_mem_range_ιFin_iff D₁]
  let z : ↥(pullback (toBase R F j) (baseMap R κ)) :=
    (es D₁).base ((pullback.fst (es D₁) (es D₂)).base p)
  have hz₁ : z ∈ Set.range (es D₁).base := ⟨_, rfl⟩
  have hz₂ : z ∈ Set.range (es D₂).base := by
    refine ⟨(pullback.snd (es D₁) (es D₂)).base p, ?_⟩
    change (pullback.snd (es D₁) (es D₂) ≫ es D₂).base p = (pullback.fst (es D₁) (es D₂) ≫ es D₁).base p
    rw [pullback.condition]
  change (pullback.fst (toBase R F j) (baseMap R κ)).base z ∈ Set.range (ιFin R F j).base
  rcases mem_range_ιFin_or_mem_range_ιInf R F j ((pullback.fst (toBase R F j) (baseMap R κ)).base z)
    with hx | hx
  · exact hx
  ·
    have hzg : z ∈ Set.range (gInf D₁).base := by rw [range_gInf]; exact hx
    obtain ⟨w, hw⟩ := hzg
    rw [← hw] at hz₁ hz₂ ⊢
    have hle := ker_sup_ker_le_of_mem_range D₁ D₂ w hz₁ hz₂
    have hj := hmid _ hle

    have hcond : (pullback.fst (toBase R F j) (baseMap R κ)).base ((gInf D₁).base w) =
        (TwoChartIntegralModel.ιInf R F j).base
          ((pullback.fst (TwoChartIntegralModel.ιInf R F j)
            (pullback.fst (toBase R F j) (baseMap R κ))).base w) := by
      change (gInf D₁ ≫ pullback.fst (toBase R F j) (baseMap R κ)).base w =
        (pullback.fst (TwoChartIntegralModel.ιInf R F j) (pullback.fst (toBase R F j) (baseMap R κ)) ≫
          TwoChartIntegralModel.ιInf R F j).base w
      rw [pullback.condition]
    rw [hcond, tc_ιInf_mem_range_ιFin_iff]
    have hw : (pullback.fst (TwoChartIntegralModel.ιInf R F j)
        (pullback.fst (toBase R F j) (baseMap R κ))).base w =
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ))).base ((isoInf D₁).hom.base w) := by
      change _ = ((isoInf D₁).hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).base w
      rw [isoInf_hom_SpecMap_includeLeft]
    rw [hw]
    exact hj

theorem natCard_pullback_es
    (hmid : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ⊔ D₂.IInf ≤ 𝔮.asIdeal →
        (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) ∉ 𝔮.asIdeal) :
    Nat.card ↥(pullback (es D₁) (es D₂)) =
      Nat.card (PrimeSpectrum
        ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ (D₁.IFin ⊔ D₂.IFin))) := by

  let m : pullback (pullback.snd (es D₁) (gFin D₁)) (pullback.snd (es D₂) (gFin D₂)) ⟶
      pullback (es D₁) (es D₂) :=
    pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (gFin D₁)
      pullback.condition.symm pullback.condition.symm
  haveI : IsOpenImmersion m := (pairCover D₁ D₂).map_prop true
  have hsurj : Function.Surjective m.base := by
    intro p
    have hp : p ∈ Set.range m := by
      rw [Scheme.Pullback.range_map]
      refine ⟨?_, ?_⟩
      · change (pullback.fst (es D₁) (es D₂)).base p ∈ Set.range (pullback.fst (es D₁) (gFin D₁)).base
        rw [range_pullback_fst_gFin]
        exact fst_mem_range_ι₀ D₁ D₂ hmid p
      · change (pullback.snd (es D₁) (es D₂)).base p ∈ Set.range (pullback.fst (es D₂) (gFin D₂)).base
        rw [range_pullback_fst_gFin]
        have h := fst_mem_range_ι₀ D₂ D₁ (fun 𝔮 h𝔮 => hmid 𝔮 (by rw [sup_comm]; exact h𝔮))
          ((pullbackSymmetry (es D₁) (es D₂)).hom.base p)
        change ((pullbackSymmetry (es D₁) (es D₂)).hom ≫ pullback.fst (es D₂) (es D₁)).base p ∈ _ at h
        rwa [pullbackSymmetry_hom_comp_fst] at h
    exact hp
  have hbij : Function.Bijective m.base := ⟨m.isOpenEmbedding.injective, hsurj⟩
  rw [← Nat.card_eq_of_bijective _ hbij,
    ← natCard_pullback_spec_quotient D₁.IFin D₂.IFin]
  exact Nat.card_congr (asIso (finCompare D₁ D₂)).schemeIsoToHomeo.toEquiv

end Pair
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

section PairCover

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

variable (D₁ D₂ : GlueDatum R F j κ t)

theorem gFin_mem_range_es_iff_IFin_le (D : GlueDatum R F j κ t) (z : PFin D) :
    (gFin D).base z ∈ Set.range (es D).base ↔ D.IFin ≤ ((isoFin D).hom.base z).asIdeal :=
  (gFin_mem_range_es_iff D z).trans (mem_range_φFin_iff D z)

theorem gInf_mem_range_es_iff_IInf_le (D : GlueDatum R F j κ t) (z : PInf D) :
    (gInf D).base z ∈ Set.range (es D).base ↔ D.IInf ≤ ((isoInf D).hom.base z).asIdeal :=
  (gInf_mem_range_es_iff D z).trans (mem_range_φInf_iff D z)

theorem forall_mem_range_es_or
    (hFin : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] κ),
      D₁.IFin ≤ 𝔮.asIdeal ∨ D₂.IFin ≤ 𝔮.asIdeal)
    (hInf : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ≤ 𝔮.asIdeal ∨ D₂.IInf ≤ 𝔮.asIdeal) :
    ∀ x : ↥(pullback (toBase R F j) (baseMap R κ)),
      x ∈ Set.range (es D₁).base ∨ x ∈ Set.range (es D₂).base := by
  intro x
  obtain ⟨i, y, hy⟩ := (fibreCover D₁).exists_eq x
  cases i with
  | false =>
    change (gInf D₁).base y = x at hy
    rw [← hy]
    rcases hInf ((isoInf D₁).hom.base y) with h | h
    · exact Or.inl ((gInf_mem_range_es_iff_IInf_le D₁ y).mpr h)
    · exact Or.inr ((gInf_mem_range_es_iff_IInf_le D₂ y).mpr h)
  | true =>
    change (gFin D₁).base y = x at hy
    rw [← hy]
    rcases hFin ((isoFin D₁).hom.base y) with h | h
    · exact Or.inl ((gFin_mem_range_es_iff_IFin_le D₁ y).mpr h)
    · exact Or.inr ((gFin_mem_range_es_iff_IFin_le D₂ y).mpr h)

omit [Fact (t ≠ 0)] in

theorem GlueDatum.isPrime_IFin (D : GlueDatum R F j κ t) : D.IFin.IsPrime :=
  RingHom.ker_isPrime D.θFin

omit [Fact (t ≠ 0)] in
theorem GlueDatum.isPrime_IInf (D : GlueDatum R F j κ t) : D.IInf.IsPrime :=
  RingHom.ker_isPrime D.θInf

def genFin (D : GlueDatum R F j κ t) : PFin D :=
  (isoFin D).inv.base ⟨D.IFin, D.isPrime_IFin⟩

omit [Fact (t ≠ 0)] in
theorem isoFin_hom_genFin (D : GlueDatum R F j κ t) :
    (isoFin D).hom.base (genFin D) = ⟨D.IFin, D.isPrime_IFin⟩ := by
  change ((isoFin D).inv ≫ (isoFin D).hom).base _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem gFin_genFin_mem_range_es (D : GlueDatum R F j κ t) :
    (gFin D).base (genFin D) ∈ Set.range (es D).base := by
  rw [gFin_mem_range_es_iff_IFin_le, isoFin_hom_genFin]

theorem IFin_le_of_genFin_mem_range (h : (gFin D₁).base (genFin D₁) ∈ Set.range (es D₂).base) :
    D₂.IFin ≤ D₁.IFin := by
  have h' := (gFin_mem_range_es_iff_IFin_le D₂ (genFin D₁)).mp h
  have e : (isoFin D₂).hom.base (genFin D₁) = ⟨D₁.IFin, D₁.isPrime_IFin⟩ := isoFin_hom_genFin D₁
  rwa [e] at h'

theorem range_es_ne (hne : D₁.IFin ≠ D₂.IFin) :
    Set.range (es D₁).base ≠ Set.range (es D₂).base := by
  intro heq
  apply hne
  refine le_antisymm ?_ ?_
  · exact IFin_le_of_genFin_mem_range D₂ D₁ (heq ▸ gFin_genFin_mem_range_es D₂)
  · exact IFin_le_of_genFin_mem_range D₁ D₂ (heq ▸ gFin_genFin_mem_range_es D₁)

end PairCover
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

section PairHmid

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

variable (D₁ D₂ : GlueDatum R F j κ t)

omit [Fact (t ≠ 0)] in

theorem hmid_of_sup_eq_top
    (hsep : D₁.IInf ⊔ D₂.IInf ⊔ Ideal.span {jInvChartInf R F j ⊗ₜ[R] (1 : κ)} = ⊤) :
    ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ⊔ D₂.IInf ≤ 𝔮.asIdeal → (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) ∉ 𝔮.asIdeal := by
  intro 𝔮 hle hmem
  apply 𝔮.2.ne_top
  rw [eq_top_iff, ← hsep]
  exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hmem)

abbrev mFin : pullback (pullback.snd (es D₁) (gFin D₁)) (pullback.snd (es D₂) (gFin D₂)) ⟶
    pullback (es D₁) (es D₂) :=
  pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (gFin D₁)
    pullback.condition.symm pullback.condition.symm

scoped instance isOpenImmersion_mFin : IsOpenImmersion (mFin D₁ D₂) := (pairCover D₁ D₂).map_prop true

theorem surjective_mFin
    (hmid : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ⊔ D₂.IInf ≤ 𝔮.asIdeal → (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) ∉ 𝔮.asIdeal) :
    Function.Surjective (mFin D₁ D₂).base := by
  intro p
  have hp : p ∈ Set.range (mFin D₁ D₂) := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · change (pullback.fst (es D₁) (es D₂)).base p ∈ Set.range (pullback.fst (es D₁) (gFin D₁)).base
      rw [range_pullback_fst_gFin]
      exact fst_mem_range_ι₀ D₁ D₂ hmid p
    · change (pullback.snd (es D₁) (es D₂)).base p ∈ Set.range (pullback.fst (es D₂) (gFin D₂)).base
      rw [range_pullback_fst_gFin]
      have h := fst_mem_range_ι₀ D₂ D₁ (fun 𝔮 h𝔮 => hmid 𝔮 (by rw [sup_comm]; exact h𝔮))
        ((pullbackSymmetry (es D₁) (es D₂)).hom.base p)
      change ((pullbackSymmetry (es D₁) (es D₂)).hom ≫ pullback.fst (es D₂) (es D₁)).base p ∈ _ at h
      rwa [pullbackSymmetry_hom_comp_fst] at h
  exact hp

theorem isIso_mFin
    (hmid : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ⊔ D₂.IInf ≤ 𝔮.asIdeal → (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) ∉ 𝔮.asIdeal) :
    IsIso (mFin D₁ D₂) :=
  (isIso_iff_isOpenImmersion_and_epi_base _).mpr
    ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr (surjective_mFin D₁ D₂ hmid)⟩

theorem isReduced_pairFin
    (hFin : _root_.IsReduced ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ (D₁.IFin ⊔ D₂.IFin))) :
    IsReduced (pullback (pullback.snd (es D₁) (gFin D₁)) (pullback.snd (es D₂) (gFin D₂))) := by
  haveI := (isReduced_pullback_spec_quotient_iff D₁.IFin D₂.IFin).mpr hFin
  exact isReduced_of_isOpenImmersion (finCompare D₁ D₂)

theorem isReduced_pullback_es_of_hmid
    (hmid : ∀ 𝔮 : PrimeSpectrum (↥(chartAlgInf R F j) ⊗[R] κ),
      D₁.IInf ⊔ D₂.IInf ≤ 𝔮.asIdeal → (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) ∉ 𝔮.asIdeal)
    (hFin : _root_.IsReduced ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ (D₁.IFin ⊔ D₂.IFin))) :
    IsReduced (pullback (es D₁) (es D₂)) := by
  haveI := isReduced_pairFin D₁ D₂ hFin
  haveI := isIso_mFin D₁ D₂ hmid
  exact isReduced_of_isOpenImmersion (inv (mFin D₁ D₂))

theorem natCard_pullback_es_of_sup_eq_top
    (hsep : D₁.IInf ⊔ D₂.IInf ⊔ Ideal.span {jInvChartInf R F j ⊗ₜ[R] (1 : κ)} = ⊤) :
    Nat.card ↥(pullback (es D₁) (es D₂)) =
      Nat.card (PrimeSpectrum ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ (D₁.IFin ⊔ D₂.IFin))) :=
  natCard_pullback_es D₁ D₂ (hmid_of_sup_eq_top D₁ D₂ hsep)

theorem isReduced_pullback_es_of_sup_eq_top
    (hsep : D₁.IInf ⊔ D₂.IInf ⊔ Ideal.span {jInvChartInf R F j ⊗ₜ[R] (1 : κ)} = ⊤)
    (hFin : _root_.IsReduced ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸ (D₁.IFin ⊔ D₂.IFin))) :
    IsReduced (pullback (es D₁) (es D₂)) :=
  isReduced_pullback_es_of_hmid D₁ D₂ (hmid_of_sup_eq_top D₁ D₂ hsep) hFin

end PairHmid
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

section Sec

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

variable (ψ : ↥(chartAlgInf R F j) →ₐ[R] R)

variable (κ) in

def secChar : ↥(chartAlgInf R F j) ⊗[R] κ →ₐ[R] κ :=
  Algebra.TensorProduct.lift ((Algebra.ofId R κ).comp ψ) (AlgHom.id R κ) (fun _ _ => Commute.all _ _)

omit [Fact (j ≠ 0)] in
@[scoped simp]
theorem secChar_tmul (b : ↥(chartAlgInf R F j)) (c : κ) :
    secChar κ ψ (b ⊗ₜ[R] c) = algebraMap R κ (ψ b) * c := by
  simp [secChar, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

omit [Fact (j ≠ 0)] in
theorem secChar_comp_includeLeftRingHom :
    (secChar κ ψ).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (algebraMap R κ).comp ψ.toRingHom := by
  ext b
  simp [Algebra.TensorProduct.includeLeftRingHom_apply]

omit [Fact (j ≠ 0)] in
theorem secChar_comp_includeRight :
    (secChar κ ψ).toRingHom.comp
        ((Algebra.TensorProduct.includeRight :
            κ →ₐ[R] ↥(chartAlgInf R F j) ⊗[R] κ) : κ →+* ↥(chartAlgInf R F j) ⊗[R] κ) =
      RingHom.id κ := by
  ext c
  simp [Algebra.TensorProduct.includeRight_apply]

abbrev secInf : Spec (CommRingCat.of R) ⟶ TwoChartIntegralModel R F j :=
  Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ TwoChartIntegralModel.ιInf R F j

theorem secInf_toBase : secInf ψ ≫ toBase R F j = 𝟙 _ := by
  rw [Category.assoc, ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1
  ext a
  simp

variable (x : Spec (CommRingCat.of κ) ⟶ pullback (toBase R F j) (baseMap R κ))
  (hx₁ : x ≫ pullback.fst _ _ = baseMap R κ ≫ secInf ψ)
  (hx₂ : x ≫ pullback.snd _ _ = 𝟙 _)

def secW (D : GlueDatum R F j κ t) : Spec (CommRingCat.of κ) ⟶ PInf D :=
  pullback.lift (baseMap R κ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) x
    (by rw [hx₁, Category.assoc])

variable (D : GlueDatum R F j κ t)

omit [Fact (t ≠ 0)] in
@[reassoc (attr := simp)]
theorem secW_fst : secW ψ x hx₁ D ≫ pullback.fst _ _ =
    baseMap R κ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) := pullback.lift_fst _ _ _

omit [Fact (t ≠ 0)] in
@[reassoc (attr := simp)]
theorem secW_gInf : secW ψ x hx₁ D ≫ gInf D = x := pullback.lift_snd _ _ _

omit [Fact (t ≠ 0)] in
include hx₁ hx₂ in

theorem SpecMap_secChar_eq :
    Spec.map (CommRingCat.ofHom (secChar κ ψ).toRingHom) ≫
        (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv =
      secW ψ x hx₁ D ≫
        (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
          (pullback.congrHom (ιInf_toBase R F j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      secChar_comp_includeLeftRingHom, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, secW_fst]
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      secChar_comp_includeRight, CommRingCat.ofHom_id]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, secW_gInf_assoc, hx₂]
    exact Spec.map_id _

omit [Fact (t ≠ 0)] in
include hx₁ hx₂ in
theorem secW_isoInf :
    secW ψ x hx₁ D ≫ (isoInf D).hom = Spec.map (CommRingCat.ofHom (secChar κ ψ).toRingHom) := by
  calc secW ψ x hx₁ D ≫ (isoInf D).hom
      = (secW ψ x hx₁ D ≫
          (pullbackRightPullbackFstIso (toBase R F j) (baseMap R κ) (TwoChartIntegralModel.ιInf R F j)).hom ≫
            (pullback.congrHom (ιInf_toBase R F j) rfl).hom) ≫
          (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by
        simp only [isoInf, Iso.trans_hom, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (secChar κ ψ).toRingHom) ≫
          (pullbackSpecIso R ↥(chartAlgInf R F j) κ).inv) ≫
          (pullbackSpecIso R ↥(chartAlgInf R F j) κ).hom := by rw [SpecMap_secChar_eq ψ x hx₁ hx₂ D]
    _ = Spec.map (CommRingCat.ofHom (secChar κ ψ).toRingHom) := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [Fact (t ≠ 0)] in
include hx₁ hx₂ in

theorem isoInf_secW_asIdeal (pt : Spec (CommRingCat.of κ)) :
    ((isoInf D).hom.base ((secW ψ x hx₁ D).base pt)).asIdeal =
      RingHom.ker (secChar κ ψ).toRingHom := by
  have h : (isoInf D).hom.base ((secW ψ x hx₁ D).base pt) =
      (Spec.map (CommRingCat.ofHom (secChar κ ψ).toRingHom)).base pt := by
    change (secW ψ x hx₁ D ≫ (isoInf D).hom).base pt = _
    rw [secW_isoInf ψ x hx₁ hx₂ D]
  have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [h, RingHom.ker_eq_comap_bot, ← hpt]
  rfl

include hx₁ hx₂ in

theorem mem_range_es_iff_IInf_le_ker_secChar (pt : Spec (CommRingCat.of κ)) :
    x.base pt ∈ Set.range (es D).base ↔ D.IInf ≤ RingHom.ker (secChar κ ψ).toRingHom := by
  have hw : x.base pt = (gInf D).base ((secW ψ x hx₁ D).base pt) := by
    change _ = (secW ψ x hx₁ D ≫ gInf D).base pt
    rw [secW_gInf]
  rw [hw, gInf_mem_range_es_iff_IInf_le, isoInf_secW_asIdeal ψ x hx₁ hx₂ D pt]

include hx₁ hx₂ in

theorem range_subset_range_es_iff :
    Set.range x.base ⊆ Set.range (es D).base ↔ D.IInf ≤ RingHom.ker (secChar κ ψ).toRingHom := by
  let pt₀ : Spec (CommRingCat.of κ) := ⟨⊥, Ideal.isPrime_bot⟩
  constructor
  · intro h
    exact (mem_range_es_iff_IInf_le_ker_secChar ψ x hx₁ hx₂ D pt₀).mp (h ⟨pt₀, rfl⟩)
  · rintro h _ ⟨pt, rfl⟩
    exact (mem_range_es_iff_IInf_le_ker_secChar ψ x hx₁ hx₂ D pt).mpr h

include hx₁ hx₂ in

theorem disjoint_range_es_of_not_le (h : ¬ D.IInf ≤ RingHom.ker (secChar κ ψ).toRingHom) :
    Disjoint (Set.range x.base) (Set.range (es D).base) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨pt, rfl⟩ hmem
  exact h ((mem_range_es_iff_IInf_le_ker_secChar ψ x hx₁ hx₂ D pt).mp hmem)

end Sec
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

end GLUECI
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace TensorAdapt

open AlgebraicCurve AlgebraicCurve.CurveModel

section ChartRing

variable (κ : Type) [Field κ]

theorem aeval_X_eq_algebraMap (f : κ[X]) :
    Polynomial.aeval (RatFunc.X : RatFunc κ) f = algebraMap κ[X] (RatFunc κ) f := by
  rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left, AlgHom.coe_id, id]

theorem aeval_X_injective :
    Function.Injective (Polynomial.aeval (RatFunc.X : RatFunc κ) : κ[X] →ₐ[κ] RatFunc κ) := by
  intro f g h
  apply RatFunc.algebraMap_injective (K := κ)
  rwa [← aeval_X_eq_algebraMap, ← aeval_X_eq_algebraMap]

theorem isIntegral_polynomial_of_isIntegral_adjoin {x : RatFunc κ}
    (hx : IsIntegral ↥(Algebra.adjoin κ ({RatFunc.X} : Set (RatFunc κ))) x) : IsIntegral κ[X] x := by
  set S := Algebra.adjoin κ ({RatFunc.X} : Set (RatFunc κ)) with hS
  have hrange : S = (Polynomial.aeval (RatFunc.X : RatFunc κ)).range :=
    Algebra.adjoin_singleton_eq_range_aeval κ (RatFunc.X : RatFunc κ)
  let e : κ[X] ≃ₐ[κ] ↥S :=
    (AlgEquiv.ofInjective _ (aeval_X_injective κ)).trans (Subalgebra.equivOfEq _ _ hrange.symm)
  have he : ∀ f : κ[X], ((e f : ↥S) : RatFunc κ) = algebraMap κ[X] (RatFunc κ) f := fun f =>
    (aeval_X_eq_algebraMap κ f)
  letI : Algebra κ[X] ↥S := (e : κ[X] →ₐ[κ] ↥S).toRingHom.toAlgebra
  haveI : IsScalarTower κ[X] ↥S (RatFunc κ) := IsScalarTower.of_algebraMap_eq fun f => by
    show algebraMap κ[X] (RatFunc κ) f = ((e f : ↥S) : RatFunc κ)
    rw [he]
  haveI : Algebra.IsIntegral κ[X] ↥S := ⟨fun s => by
    obtain ⟨f, rfl⟩ := e.surjective s
    exact isIntegral_algebraMap (R := κ[X]) (A := ↥S) (x := f)⟩
  exact isIntegral_trans x hx

theorem mem_chartRing_X_iff (x : RatFunc κ) :
    x ∈ chartRing κ ({RatFunc.X} : Set (RatFunc κ)) ↔ ∃ f : κ[X], algebraMap κ[X] (RatFunc κ) f = x := by
  constructor
  · intro hx
    rw [mem_chartRing_iff] at hx
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_polynomial_of_isIntegral_adjoin κ hx)
  · rintro ⟨f, rfl⟩
    rw [← aeval_X_eq_algebraMap]
    exact adjoin_le_chartRing κ _ (Polynomial.aeval_mem_adjoin_singleton κ _)

def tX : ↥(chartRing κ ({RatFunc.X} : Set (RatFunc κ))) := tChart κ (RatFunc.X : RatFunc κ)

@[scoped simp] theorem coe_tX : (tX κ : RatFunc κ) = RatFunc.X := rfl

theorem eq_aeval_tX (y : ↥(chartRing κ ({RatFunc.X} : Set (RatFunc κ)))) :
    ∃ f : κ[X], y = Polynomial.aeval (tX κ) f := by
  obtain ⟨f, hf⟩ := (mem_chartRing_X_iff κ y).mp y.2
  refine ⟨f, Subtype.ext ?_⟩
  rw [← hf, ← aeval_X_eq_algebraMap]
  exact Polynomial.aeval_algHom_apply ((chartRing κ ({RatFunc.X} : Set (RatFunc κ))).val) (tX κ) f

end ChartRing
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

section InvChart

variable (κ : Type) [Field κ]

theorem transcendental_Xinv : Transcendental κ ((RatFunc.X : RatFunc κ)⁻¹) := fun h =>
  RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)

theorem aeval_Xinv_injective :
    Function.Injective (Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) : κ[X] →ₐ[κ] RatFunc κ) :=
  transcendental_iff_injective.mp (transcendental_Xinv κ)

def σHom : RatFunc κ →ₐ[κ] RatFunc κ :=
  RatFunc.liftAlgHom (Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_Xinv_injective κ))

theorem σHom_algebraMap (f : κ[X]) :
    σHom κ (algebraMap κ[X] (RatFunc κ) f) = Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) f := by
  have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_Xinv_injective κ)) f 1
  rw [map_one, div_one, map_one, div_one] at h
  exact h

@[scoped simp]
theorem σHom_X : σHom κ RatFunc.X = (RatFunc.X : RatFunc κ)⁻¹ := by
  have h := σHom_algebraMap κ Polynomial.X
  rwa [Polynomial.aeval_X, RatFunc.algebraMap_X] at h

@[scoped simp]
theorem σHom_Xinv : σHom κ (RatFunc.X : RatFunc κ)⁻¹ = RatFunc.X := by
  rw [map_inv₀, σHom_X, inv_inv]

theorem σHom_comp_σHom : (σHom κ).comp (σHom κ) = AlgHom.id κ (RatFunc κ) := by
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors κ[X]) (Polynomial.ringHom_ext (fun a => ?_) ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
      Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, AlgHom.commutes]
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
      RatFunc.algebraMap_X, AlgHom.comp_apply, σHom_X, σHom_Xinv, AlgHom.id_apply]

theorem σHom_σHom (x : RatFunc κ) : σHom κ (σHom κ x) = x :=
  AlgHom.congr_fun (σHom_comp_σHom κ) x

def σ : RatFunc κ ≃ₐ[κ] RatFunc κ :=
  AlgEquiv.ofAlgHom (σHom κ) (σHom κ) (σHom_comp_σHom κ) (σHom_comp_σHom κ)

theorem σ_apply (x : RatFunc κ) : σ κ x = σHom κ x := rfl

@[scoped simp]
theorem σ_X : σ κ RatFunc.X = (RatFunc.X : RatFunc κ)⁻¹ := σHom_X κ

@[scoped simp]
theorem σ_Xinv : σ κ (RatFunc.X : RatFunc κ)⁻¹ = RatFunc.X := σHom_Xinv κ

@[scoped simp]
theorem σ_σ (x : RatFunc κ) : σ κ (σ κ x) = x := σHom_σHom κ x

theorem σ_symm : (σ κ).symm = σ κ := rfl

theorem σ_aeval_X (f : κ[X]) :
    σ κ (Polynomial.aeval (RatFunc.X : RatFunc κ) f) = Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) f := by
  rw [σ_apply, ← Polynomial.aeval_algHom_apply, σHom_X]

theorem σ_aeval_Xinv (f : κ[X]) :
    σ κ (Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) f) = Polynomial.aeval (RatFunc.X : RatFunc κ) f := by
  rw [σ_apply, ← Polynomial.aeval_algHom_apply, σHom_Xinv]

theorem map_mem_chartRing {L : Type} [Field L] [Algebra κ L] (e : L →ₐ[κ] L) (S : Set L)
    {x : L} (hx : x ∈ chartRing κ S) : e x ∈ chartRing κ (e '' S) := by
  rw [mem_chartRing_iff] at hx ⊢
  have hmap : ∀ a ∈ Algebra.adjoin κ S, e a ∈ Algebra.adjoin κ (e '' S) := fun a ha => by
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
  let φ : ↥(Algebra.adjoin κ S) →+* ↥(Algebra.adjoin κ (e '' S)) :=
    (e.toRingHom.comp (Algebra.adjoin κ S).val.toRingHom).codRestrict
      (Algebra.adjoin κ (e '' S)).toSubring (fun a => hmap a a.2)
  exact hx.map_of_comp_eq φ e.toRingHom (RingHom.ext fun _ => rfl)

theorem mem_chartRing_Xinv_iff (x : RatFunc κ) :
    x ∈ chartRing κ ({(RatFunc.X : RatFunc κ)⁻¹} : Set (RatFunc κ)) ↔
      ∃ f : κ[X], Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) f = x := by
  constructor
  · intro hx
    have h1 : σ κ x ∈ chartRing κ ({RatFunc.X} : Set (RatFunc κ)) := by
      have h := map_mem_chartRing κ (σHom κ) _ hx
      rwa [Set.image_singleton, σHom_Xinv] at h
    obtain ⟨f, hf⟩ := (mem_chartRing_X_iff κ _).mp h1
    refine ⟨f, ?_⟩
    rw [← aeval_X_eq_algebraMap] at hf
    rw [← σ_σ κ x, ← hf, σ_aeval_X]
  · rintro ⟨f, rfl⟩
    exact adjoin_le_chartRing κ _ (Polynomial.aeval_mem_adjoin_singleton κ _)

def tXinv : ↥(chartRing κ ({(RatFunc.X : RatFunc κ)⁻¹} : Set (RatFunc κ))) :=
  tChart κ ((RatFunc.X : RatFunc κ)⁻¹)

@[scoped simp] theorem coe_tXinv : (tXinv κ : RatFunc κ) = (RatFunc.X : RatFunc κ)⁻¹ := rfl

theorem eq_aeval_tXinv (y : ↥(chartRing κ ({(RatFunc.X : RatFunc κ)⁻¹} : Set (RatFunc κ)))) :
    ∃ f : κ[X], y = Polynomial.aeval (tXinv κ) f := by
  obtain ⟨f, hf⟩ := (mem_chartRing_Xinv_iff κ y).mp y.2
  refine ⟨f, Subtype.ext ?_⟩
  rw [← hf]
  exact Polynomial.aeval_algHom_apply
    ((chartRing κ ({(RatFunc.X : RatFunc κ)⁻¹} : Set (RatFunc κ))).val) (tXinv κ) f

end InvChart
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

section Adapter

variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [Algebra (ZMod p) κ]
  {A : Type} [CommRing A] {B : Type} [CommRing B] (π : A →+* B) (e : B ≃+* (ZMod p)[X])
  (t : RatFunc κ)

def ψq : B →+* κ[X] := (Polynomial.mapRingHom (algebraMap (ZMod p) κ)).comp e.toRingHom

def ψ : A →+* RatFunc κ := ((Polynomial.aeval t : κ[X] →ₐ[κ] RatFunc κ).toRingHom.comp (ψq p κ e)).comp π

def ψqₐ : B →ₐ[ℤ] κ[X] := { ψq p κ e with commutes' := fun n => by simp }

def ψₐ : A →ₐ[ℤ] RatFunc κ := { ψ p κ π e t with commutes' := fun n => by simp }

def πₐ : A →ₐ[ℤ] B := { π with commutes' := fun n => by simp }

def Θq : κ ⊗[ℤ] B →ₐ[κ] κ[X] :=
  Algebra.TensorProduct.lift (Algebra.ofId κ κ[X]) (ψqₐ p κ e) (fun _ _ => Commute.all _ _)

def Θ : κ ⊗[ℤ] A →ₐ[κ] RatFunc κ :=
  Algebra.TensorProduct.lift (Algebra.ofId κ (RatFunc κ)) (ψₐ p κ π e t) (fun _ _ => Commute.all _ _)

theorem Θ_tmul (a : κ) (b : A) : Θ p κ π e t (a ⊗ₜ b) = algebraMap κ (RatFunc κ) a * ψ p κ π e t b := by
  rw [Θ, Algebra.TensorProduct.lift_tmul]; rfl

theorem Θq_tmul (a : κ) (b : B) : Θq p κ e (a ⊗ₜ b) = Polynomial.C a * ψq p κ e b := by
  rw [Θq, Algebra.TensorProduct.lift_tmul]; rfl

theorem ψ_apply (b : A) : ψ p κ π e t b = Polynomial.aeval t (ψq p κ e (π b)) := rfl

theorem Θ_eq (z : κ ⊗[ℤ] A) :
    Θ p κ π e t z = Polynomial.aeval t
      (Θq p κ e (Algebra.TensorProduct.map (AlgHom.id ℤ κ) (πₐ π) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [Θ_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Θq_tmul, map_mul, ψ_apply]
      congr 1 <;> simp
  | add x y hx hy => simp only [map_add, hx, hy]

def Θqinv : κ[X] →ₐ[κ] κ ⊗[ℤ] B := Polynomial.aeval ((1 : κ) ⊗ₜ[ℤ] e.symm Polynomial.X)

theorem Θqinv_C (a : κ) : Θqinv p κ e (Polynomial.C a) = a ⊗ₜ[ℤ] (1 : B) := by
  rw [Θqinv, Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]

theorem Θqinv_ψq (b : B) : Θqinv p κ e (ψq p κ e b) = (1 : κ) ⊗ₜ[ℤ] b := by

  obtain ⟨q, rfl⟩ : ∃ q : (ZMod p)[X], e.symm q = b := ⟨e b, e.symm_apply_apply b⟩
  have h1 : (Θqinv p κ e).toRingHom.comp ((ψq p κ e).comp e.symm.toRingHom) =
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := B)).toRingHom.comp e.symm.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c

      have := RingHom.ext_zmod
        (((Θqinv p κ e).toRingHom.comp ((ψq p κ e).comp e.symm.toRingHom)).comp Polynomial.C)
        (((Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := B)).toRingHom.comp e.symm.toRingHom).comp Polynomial.C)
      exact RingHom.congr_fun this c
    · show Θqinv p κ e (ψq p κ e (e.symm Polynomial.X)) = (1 : κ) ⊗ₜ[ℤ] e.symm Polynomial.X
      rw [ψq, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e.apply_symm_apply,
        Polynomial.coe_mapRingHom, Polynomial.map_X, Θqinv, Polynomial.aeval_X]
  have := RingHom.congr_fun h1 q
  simpa using this

theorem Θqinv_comp_Θq : (Θqinv p κ e).comp (Θq p κ e) = AlgHom.id κ _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · ext b
    show Θqinv p κ e (Θq p κ e ((1 : κ) ⊗ₜ[ℤ] b)) = (1 : κ) ⊗ₜ[ℤ] b
    rw [Θq_tmul, Polynomial.C_1, one_mul, Θqinv_ψq]

theorem Θq_injective : Function.Injective (Θq p κ e) := by
  intro x y h
  have := congrArg (Θqinv p κ e) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, Θqinv_comp_Θq, AlgHom.id_apply, AlgHom.id_apply] at this

variable (hinj : Function.Injective (Polynomial.aeval t : κ[X] →ₐ[κ] RatFunc κ))
  (hchart : ∀ x : RatFunc κ, x ∈ chartRing κ ({t} : Set (RatFunc κ)) ↔ ∃ f : κ[X], Polynomial.aeval t f = x)

theorem Θq_comp_Θqinv : (Θq p κ e).comp (Θqinv p κ e) = AlgHom.id κ _ := by
  apply Polynomial.algHom_ext
  show Θq p κ e (Θqinv p κ e Polynomial.X) = Polynomial.X
  rw [Θqinv, Polynomial.aeval_X, Θq_tmul, Polynomial.C_1, one_mul, ψq, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e.apply_symm_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]

theorem Θq_surjective : Function.Surjective (Θq p κ e) := by
  intro f
  exact ⟨Θqinv p κ e f, by rw [← AlgHom.comp_apply, Θq_comp_Θqinv, AlgHom.id_apply]⟩

def θP : κ ⊗[ℤ] A →+* κ[X] :=
  (Θq p κ e).toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id ℤ κ) (πₐ π)).toRingHom

theorem θP_tmul (a : κ) (b : A) : θP p κ π e (a ⊗ₜ[ℤ] b) = Polynomial.C a * (e (π b)).map (algebraMap (ZMod p) κ) := by
  show Θq p κ e (Algebra.TensorProduct.map (AlgHom.id ℤ κ) (πₐ π) (a ⊗ₜ[ℤ] b)) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Θq_tmul]
  rfl

theorem Θ_eq_aeval_θP (z : κ ⊗[ℤ] A) : Θ p κ π e t z = Polynomial.aeval t (θP p κ π e z) := Θ_eq p κ π e t z

theorem ker_θP (hπ : Function.Surjective π) :
    RingHom.ker (θP p κ π e) = (RingHom.ker π).map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A)) := by
  have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id ℤ κ) (πₐ π)) =
      (RingHom.ker (πₐ π)).map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A)) :=
    Algebra.TensorProduct.lTensor_ker (πₐ π) hπ
  ext z
  rw [RingHom.mem_ker]
  show Θq p κ e (Algebra.TensorProduct.map (AlgHom.id ℤ κ) (πₐ π) z) = 0 ↔ _
  rw [map_eq_zero_iff _ (Θq_injective p κ e), ← RingHom.mem_ker, hker]
  rfl

theorem θP_surjective (hπ : Function.Surjective π) : Function.Surjective (θP p κ π e) := by
  intro f
  obtain ⟨w, rfl⟩ := Θq_surjective p κ e f
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
      obtain ⟨b₀, rfl⟩ := hπ b
      exact ⟨a ⊗ₜ b₀, rfl⟩
  | add x y hx hy =>
      obtain ⟨x₀, hx₀⟩ := hx
      obtain ⟨y₀, hy₀⟩ := hy
      exact ⟨x₀ + y₀, by rw [map_add, hx₀, hy₀, map_add]⟩

include hinj in

theorem ker_Θ (hπ : Function.Surjective π) :
    RingHom.ker (Θ p κ π e t) = (RingHom.ker π).map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A)) := by
  have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id ℤ κ) (πₐ π)) =
      (RingHom.ker (πₐ π)).map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A)) :=
    Algebra.TensorProduct.lTensor_ker (πₐ π) hπ
  ext z
  rw [RingHom.mem_ker, Θ_eq, map_eq_zero_iff _ hinj,
    map_eq_zero_iff _ (Θq_injective p κ e), ← RingHom.mem_ker, hker]
  rfl

include hchart in

theorem Θ_mem (z : κ ⊗[ℤ] A) : Θ p κ π e t z ∈ chartRing κ ({t} : Set (RatFunc κ)) := by
  rw [Θ_eq, hchart]
  exact ⟨_, rfl⟩

def θ : κ ⊗[ℤ] A →ₐ[κ] ↥(chartRing κ ({t} : Set (RatFunc κ))) :=
  (Θ p κ π e t).codRestrict (chartRing κ ({t} : Set (RatFunc κ))) (Θ_mem p κ π e t hchart)

theorem coe_θ (z : κ ⊗[ℤ] A) : (θ p κ π e t hchart z : RatFunc κ) = Θ p κ π e t z := rfl

theorem coe_θ_tmul (b : A) :
    (θ p κ π e t hchart ((1 : κ) ⊗ₜ[ℤ] b) : RatFunc κ) =
      Polynomial.aeval t (Polynomial.map (algebraMap (ZMod p) κ) (e (π b))) := by
  rw [coe_θ, Θ_tmul, map_one, one_mul]; rfl

include hinj in
theorem ker_θ (hπ : Function.Surjective π) :
    RingHom.ker (θ p κ π e t hchart) = (RingHom.ker π).map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A)) := by
  rw [← ker_Θ p κ π e t hinj hπ]
  ext z
  simp only [RingHom.mem_ker]
  rw [← ZeroMemClass.coe_eq_zero, coe_θ]

def tCh : ↥(chartRing κ ({t} : Set (RatFunc κ))) := tChart κ t

@[scoped simp] theorem coe_tCh : (tCh κ t : RatFunc κ) = t := rfl

include hchart in
theorem eq_aeval_tCh (y : ↥(chartRing κ ({t} : Set (RatFunc κ)))) : ∃ f : κ[X], y = Polynomial.aeval (tCh κ t) f := by
  obtain ⟨f, hf⟩ := (hchart y).mp y.2
  refine ⟨f, Subtype.ext ?_⟩
  rw [← hf]
  exact Polynomial.aeval_algHom_apply ((chartRing κ ({t} : Set (RatFunc κ))).val) (tCh κ t) f

theorem θ_surjective (hπ : Function.Surjective π) : Function.Surjective (θ p κ π e t hchart) := by
  intro y
  obtain ⟨f, rfl⟩ := eq_aeval_tCh κ t hchart y
  obtain ⟨a, ha⟩ := hπ (e.symm Polynomial.X)
  have hX : θ p κ π e t hchart ((1 : κ) ⊗ₜ[ℤ] a) = tCh κ t := by
    apply Subtype.ext
    rw [coe_θ_tmul, ha, e.apply_symm_apply, Polynomial.map_X, Polynomial.aeval_X]
    rfl
  refine ⟨Polynomial.aeval ((1 : κ) ⊗ₜ[ℤ] a) f, ?_⟩
  rw [← Polynomial.aeval_algHom_apply, hX]

theorem hinj_X : Function.Injective (Polynomial.aeval (RatFunc.X : RatFunc κ) : κ[X] →ₐ[κ] RatFunc κ) :=
  aeval_X_injective κ

theorem hchart_X (x : RatFunc κ) :
    x ∈ chartRing κ ({RatFunc.X} : Set (RatFunc κ)) ↔ ∃ f : κ[X], Polynomial.aeval (RatFunc.X : RatFunc κ) f = x := by
  rw [mem_chartRing_X_iff]
  simp only [aeval_X_eq_algebraMap]

end Adapter
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

section MidLift

open AlgebraicCurve.TwoChartIntegralModel

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (j : F) [Fact (j ≠ 0)]
  (𝔭 : Ideal ↥(chartAlgFin ℤ F j)) (e : (↥(chartAlgFin ℤ F j) ⧸ 𝔭) ≃+* (ZMod p)[X]) (m : ℕ)

def ρ₀ : ↥(chartAlgFin ℤ F j) →+* RatFunc (ZMod p) :=
  (Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)).toRingHom.comp
    (e.toRingHom.comp (Ideal.Quotient.mk 𝔭))

theorem ρ₀_apply (b : ↥(chartAlgFin ℤ F j)) :
    ρ₀ p j 𝔭 e b = Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) (e (Ideal.Quotient.mk 𝔭 b)) := rfl

variable (hej : e (Ideal.Quotient.mk 𝔭 (jChartFin ℤ F j)) = Polynomial.X ^ m)

include hej in
theorem ρ₀_j : ρ₀ p j 𝔭 e (jChartFin ℤ F j) = RatFunc.X ^ m := by
  rw [ρ₀_apply, hej, map_pow, Polynomial.aeval_X]

include hej in
theorem isUnit_ρ₀_j : IsUnit (ρ₀ p j 𝔭 e (jChartFin ℤ F j)) := by
  rw [ρ₀_j p j 𝔭 e m hej]
  exact (isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero).pow m

def ρ₀M : ↥(chartAlgMid ℤ F j) →+* RatFunc (ZMod p) :=
  letI := (TwoChartIntegralModel.inclFin ℤ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤ F j
  IsLocalization.Away.lift (jChartFin ℤ F j) (g := ρ₀ p j 𝔭 e) (isUnit_ρ₀_j p j 𝔭 e m hej)

theorem ρ₀M_inclFin (b : ↥(chartAlgFin ℤ F j)) : ρ₀M p j 𝔭 e m hej (TwoChartIntegralModel.inclFin ℤ F j b) = ρ₀ p j 𝔭 e b := by
  letI := (TwoChartIntegralModel.inclFin ℤ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤ F j
  exact IsLocalization.Away.lift_eq (jChartFin ℤ F j) (isUnit_ρ₀_j p j 𝔭 e m hej) b

def ρ₀' : ↥(chartAlgInf ℤ F j) →+* RatFunc (ZMod p) :=
  (ρ₀M p j 𝔭 e m hej).comp (TwoChartIntegralModel.inclInf ℤ F j).toRingHom

theorem ρ₀'_mul_pow (b : ↥(chartAlgFin ℤ F j)) (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ)
    (h : (b : F) = (b' : F) * j ^ n) :
    ρ₀' p j 𝔭 e m hej b' * RatFunc.X ^ (m * n) = ρ₀ p j 𝔭 e b := by
  have hmid : TwoChartIntegralModel.inclInf ℤ F j b' * TwoChartIntegralModel.inclFin ℤ F j (jChartFin ℤ F j) ^ n =
      TwoChartIntegralModel.inclFin ℤ F j b := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, TwoChartIntegralModel.coe_chartIncl, coe_jChartFin]
    exact h.symm
  have := congrArg (ρ₀M p j 𝔭 e m hej) hmid
  rw [map_mul, map_pow, ρ₀M_inclFin, ρ₀M_inclFin, ρ₀_j p j 𝔭 e m hej, ← pow_mul] at this
  exact this

theorem ρ₀'_jInv (hm : 0 < m ∨ True) : ρ₀' p j 𝔭 e m hej (jInvChartInf ℤ F j) = (RatFunc.X ^ m)⁻¹ := by
  have h := ρ₀'_mul_pow p j 𝔭 e m hej 1 (jInvChartInf ℤ F j) 1
    (by rw [coe_jInvChartInf, pow_one, inv_mul_cancel₀ (Fact.out : j ≠ 0)]; rfl)
  rw [mul_one, map_one] at h
  exact eq_inv_of_mul_eq_one_left h

abbrev inclAdj : ↥(Algebra.adjoin ℤ ({j⁻¹} : Set F)) →ₐ[ℤ] ↥(chartAlgInf ℤ F j) :=
  Subalgebra.inclusion (adjoin_le_chartAlg ℤ F ({j⁻¹} : Set F))

theorem ρ₀'_inclAdj_mem (x : F) (hx : x ∈ Algebra.adjoin ℤ ({j⁻¹} : Set F)) :
    ρ₀' p j 𝔭 e m hej (inclAdj j ⟨x, hx⟩) ∈ Algebra.adjoin (ZMod p) ({(RatFunc.X : RatFunc (ZMod p))⁻¹} : Set (RatFunc (ZMod p))) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have : inclAdj j ⟨j⁻¹, Algebra.subset_adjoin (Set.mem_singleton _)⟩ = jInvChartInf ℤ F j := Subtype.ext rfl
      rw [this, ρ₀'_jInv p j 𝔭 e m hej (Or.inr trivial), ← inv_pow]
      exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) m
  | algebraMap r =>
      have : inclAdj j ⟨algebraMap ℤ F r, Subalgebra.algebraMap_mem _ r⟩ = algebraMap ℤ _ r := Subtype.ext rfl
      rw [this, ← RingHom.comp_apply, eq_intCast]
      exact intCast_mem _ r
  | add x y hx hy ihx ihy =>
      have : inclAdj j ⟨x + y, add_mem hx hy⟩ = inclAdj j ⟨x, hx⟩ + inclAdj j ⟨y, hy⟩ := Subtype.ext rfl
      rw [this, map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      have : inclAdj j ⟨x * y, mul_mem hx hy⟩ = inclAdj j ⟨x, hx⟩ * inclAdj j ⟨y, hy⟩ := Subtype.ext rfl
      rw [this, map_mul]; exact mul_mem ihx ihy

theorem ρ₀'_mem_chartRing (b' : ↥(chartAlgInf ℤ F j)) :
    ρ₀' p j 𝔭 e m hej b' ∈ chartRing (ZMod p) ({(RatFunc.X : RatFunc (ZMod p))⁻¹} : Set (RatFunc (ZMod p))) := by
  set S := Algebra.adjoin (ZMod p) ({(RatFunc.X : RatFunc (ZMod p))⁻¹} : Set (RatFunc (ZMod p))) with hS
  rw [mem_chartRing_iff]

  have hb : IsIntegral ↥(Algebra.adjoin ℤ ({j⁻¹} : Set F)) (b' : F) := (mem_chartAlg_iff ℤ F).mp b'.2
  obtain ⟨q, hqm, hq0⟩ := hb

  set q₁ : Polynomial ↥(chartAlgInf ℤ F j) := q.map (inclAdj j).toRingHom with hq₁
  have hq₁m : q₁.Monic := hqm.map _
  have hq₁0 : q₁.eval b' = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    change (chartAlgInf ℤ F j).val.toRingHom (q₁.eval b') = 0
    rw [← Polynomial.eval₂_hom, hq₁, Polynomial.eval₂_map]
    exact hq0

  set Q : Polynomial (RatFunc (ZMod p)) := q₁.map (ρ₀' p j 𝔭 e m hej) with hQ
  have hQm : Q.Monic := hq₁m.map _
  have hQ0 : Q.eval (ρ₀' p j 𝔭 e m hej b') = 0 := by
    rw [hQ, Polynomial.eval_map, Polynomial.eval₂_hom, hq₁0, map_zero]

  have hlift : Q ∈ Polynomial.lifts (algebraMap ↥S (RatFunc (ZMod p))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hQ, Polynomial.coeff_map, hq₁, Polynomial.coeff_map]
    refine ⟨⟨_, ρ₀'_inclAdj_mem p j 𝔭 e m hej (q.coeff i) (q.coeff i).2⟩, rfl⟩
  obtain ⟨Q', hQ'map, -, hQ'm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hQm
  refine ⟨Q', hQ'm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hQ'map, hQ0]

theorem mem_ker_ρ₀'_iff (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ) (b : ↥(chartAlgFin ℤ F j))
    (hb : (b : F) = (b' : F) * j ^ n) :
    b' ∈ RingHom.ker (ρ₀' p j 𝔭 e m hej) ↔ b ∈ 𝔭 := by
  rw [RingHom.mem_ker]
  have h1 := ρ₀'_mul_pow p j 𝔭 e m hej b b' n hb
  have hX : (RatFunc.X : RatFunc (ZMod p)) ^ (m * n) ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  constructor
  · intro h0
    rw [h0, zero_mul, ρ₀_apply, eq_comm, map_eq_zero_iff _ (aeval_X_injective (ZMod p)),
      map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  · intro hb𝔭
    have : ρ₀ p j 𝔭 e b = 0 := by
      rw [ρ₀_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hb𝔭, map_zero, map_zero]
    rw [this] at h1
    exact (mul_eq_zero.mp h1).resolve_right hX

variable (hgen : ∃ (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ) (b : ↥(chartAlgFin ℤ F j)),
    (b : F) = (b' : F) * j ^ n ∧ e (Ideal.Quotient.mk 𝔭 b) * Polynomial.X = Polynomial.X ^ (m * n))

include hgen in
theorem exists_ρ₀'_eq_Xinv : ∃ b' : ↥(chartAlgInf ℤ F j), ρ₀' p j 𝔭 e m hej b' = (RatFunc.X : RatFunc (ZMod p))⁻¹ := by
  obtain ⟨b', n, b, hb, heb⟩ := hgen
  refine ⟨b', ?_⟩
  have h1 := ρ₀'_mul_pow p j 𝔭 e m hej b b' n hb
  have h2 : ρ₀ p j 𝔭 e b * RatFunc.X = RatFunc.X ^ (m * n) := by
    have := congrArg (Polynomial.aeval (RatFunc.X : RatFunc (ZMod p))) heb
    rwa [map_mul, map_pow, Polynomial.aeval_X, ← ρ₀_apply] at this
  have hX : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 := RatFunc.X_ne_zero
  have h3 : ρ₀' p j 𝔭 e m hej b' * RatFunc.X = 1 := by
    have : ρ₀' p j 𝔭 e m hej b' * RatFunc.X * RatFunc.X ^ (m * n) = 1 * RatFunc.X ^ (m * n) := by
      rw [mul_right_comm, h1, one_mul, h2]
    exact mul_right_cancel₀ (pow_ne_zero _ hX) this
  exact eq_inv_of_mul_eq_one_left h3

include hgen in

theorem mem_range_ρ₀'_iff (y : RatFunc (ZMod p)) :
    y ∈ (ρ₀' p j 𝔭 e m hej).range ↔ ∃ f : (ZMod p)[X], Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) f = y := by
  constructor
  · rintro ⟨b', rfl⟩
    exact (mem_chartRing_Xinv_iff (ZMod p) _).mp (ρ₀'_mem_chartRing p j 𝔭 e m hej b')
  · rintro ⟨f, rfl⟩
    obtain ⟨b₀, hb₀⟩ := exists_ρ₀'_eq_Xinv p j 𝔭 e m hej hgen
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, ← hb₀,
          ← map_pow]
        refine mul_mem ?_ ⟨_, rfl⟩

        refine ⟨(c.val : ↥(chartAlgInf ℤ F j)), ?_⟩
        rw [map_natCast, ← map_natCast (algebraMap (ZMod p) (RatFunc (ZMod p))), ZMod.natCast_zmod_val]

include hgen in
theorem ρ₀'_mem_aevalRange (b' : ↥(chartAlgInf ℤ F j)) :
    ρ₀' p j 𝔭 e m hej b' ∈ (Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)).range := by
  obtain ⟨f, hf⟩ := (mem_range_ρ₀'_iff p j 𝔭 e m hej hgen _).mp ⟨b', rfl⟩
  exact ⟨f, hf⟩

def g₀ : ↥(chartAlgInf ℤ F j) →+* (ZMod p)[X] :=
  ((AlgEquiv.ofInjective _ (aeval_Xinv_injective (ZMod p))).symm : _ →ₐ[ZMod p] (ZMod p)[X]).toRingHom.comp
    ((ρ₀' p j 𝔭 e m hej).codRestrict
      (Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)).range
      (ρ₀'_mem_aevalRange p j 𝔭 e m hej hgen))

theorem aeval_g₀ (b' : ↥(chartAlgInf ℤ F j)) :
    Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) (g₀ p j 𝔭 e m hej hgen b') = ρ₀' p j 𝔭 e m hej b' := by
  set E := AlgEquiv.ofInjective _ (aeval_Xinv_injective (ZMod p)) with hE
  have key : ∀ y : ↥((Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)).range),
      Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) (E.symm y) = (y : RatFunc (ZMod p)) := by
    intro y
    have := AlgEquiv.ofInjective_apply _ (aeval_Xinv_injective (ZMod p)) (E.symm y)
    rw [← this, hE, AlgEquiv.apply_symm_apply]
  exact key _

theorem g₀_surjective : Function.Surjective (g₀ p j 𝔭 e m hej hgen) := by
  intro f
  obtain ⟨b', hb'⟩ := (mem_range_ρ₀'_iff p j 𝔭 e m hej hgen _).mpr ⟨f, rfl⟩
  refine ⟨b', aeval_Xinv_injective (ZMod p) ?_⟩
  rw [aeval_g₀, hb']

theorem ker_g₀ : RingHom.ker (g₀ p j 𝔭 e m hej hgen) = RingHom.ker (ρ₀' p j 𝔭 e m hej) := by
  ext b'
  rw [RingHom.mem_ker, RingHom.mem_ker, ← (aeval_Xinv_injective (ZMod p)).eq_iff, aeval_g₀, map_zero]

def e' : (↥(chartAlgInf ℤ F j) ⧸ RingHom.ker (ρ₀' p j 𝔭 e m hej)) ≃+* (ZMod p)[X] :=
  (Ideal.quotEquivOfEq (ker_g₀ p j 𝔭 e m hej hgen).symm).trans
    (RingHom.quotientKerEquivOfSurjective (g₀_surjective p j 𝔭 e m hej hgen))

theorem aeval_e' (b' : ↥(chartAlgInf ℤ F j)) :
    Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) (e' p j 𝔭 e m hej hgen (Ideal.Quotient.mk _ b')) =
      ρ₀' p j 𝔭 e m hej b' := by
  rw [← aeval_g₀ p j 𝔭 e m hej hgen b']
  congr 1

theorem e'_jInv : e' p j 𝔭 e m hej hgen (Ideal.Quotient.mk _ (jInvChartInf ℤ F j)) = Polynomial.X ^ m := by
  apply aeval_Xinv_injective (ZMod p)
  rw [aeval_e', ρ₀'_jInv p j 𝔭 e m hej (Or.inr trivial), map_pow, Polynomial.aeval_X, inv_pow]

variable (κ : Type) [Field κ] [Algebra (ZMod p) κ]

theorem aevalX_comp_map_injective :
    Function.Injective ((Polynomial.aeval (RatFunc.X : RatFunc κ) : κ[X] →ₐ[κ] RatFunc κ).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap (ZMod p) κ))) :=
  (aeval_X_injective κ).comp (Polynomial.map_injective _ (algebraMap (ZMod p) κ).injective)

def Φ : RatFunc (ZMod p) →+* RatFunc κ :=
  RatFunc.liftRingHom ((Polynomial.aeval (RatFunc.X : RatFunc κ) : κ[X] →ₐ[κ] RatFunc κ).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap (ZMod p) κ)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aevalX_comp_map_injective p κ))

theorem Φ_algebraMap (f : (ZMod p)[X]) :
    Φ p κ (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) f) =
      Polynomial.aeval (RatFunc.X : RatFunc κ) (f.map (algebraMap (ZMod p) κ)) := by
  have h := RatFunc.liftRingHom_apply_div
    ((Polynomial.aeval (RatFunc.X : RatFunc κ) : κ[X] →ₐ[κ] RatFunc κ).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap (ZMod p) κ)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aevalX_comp_map_injective p κ)) f 1
  rw [map_one, div_one, map_one, div_one] at h
  exact h

theorem Φ_aeval_X (f : (ZMod p)[X]) :
    Φ p κ (Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) f) =
      Polynomial.aeval (RatFunc.X : RatFunc κ) (f.map (algebraMap (ZMod p) κ)) := by
  rw [aeval_X_eq_algebraMap, Φ_algebraMap]

theorem Φ_X : Φ p κ RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, Φ_algebraMap, Polynomial.map_X, Polynomial.aeval_X]

theorem Φ_aeval_Xinv (f : (ZMod p)[X]) :
    Φ p κ (Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) f) =
      Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) (f.map (algebraMap (ZMod p) κ)) := by
  have key : (Φ p κ).comp (Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) : (ZMod p)[X] →ₐ[ZMod p] _).toRingHom =
      ((Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) : κ[X] →ₐ[κ] RatFunc κ).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap (ZMod p) κ))) := by
    apply Polynomial.ringHom_ext
    · intro c
      exact RingHom.congr_fun (RingHom.ext_zmod
        (((Φ p κ).comp (Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) : (ZMod p)[X] →ₐ[ZMod p] _).toRingHom).comp
          Polynomial.C)
        ((((Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) : κ[X] →ₐ[κ] RatFunc κ).toRingHom.comp
          (Polynomial.mapRingHom (algebraMap (ZMod p) κ)))).comp Polynomial.C)) c
    · show Φ p κ (Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) Polynomial.X) =
        Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹) (Polynomial.map (algebraMap (ZMod p) κ) Polynomial.X)
      rw [Polynomial.aeval_X, Polynomial.map_X, Polynomial.aeval_X, map_inv₀, Φ_X]
  exact RingHom.congr_fun key f

theorem compat (b : ↥(chartAlgFin ℤ F j)) (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ) (hb : (b : F) = (b' : F) * j ^ n) :
    Polynomial.aeval (RatFunc.X : RatFunc κ) ((e (Ideal.Quotient.mk 𝔭 b)).map (algebraMap (ZMod p) κ)) =
      Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹)
          ((e' p j 𝔭 e m hej hgen (Ideal.Quotient.mk _ b')).map (algebraMap (ZMod p) κ)) *
        RatFunc.X ^ (m * n) := by
  have h0 : Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) (e (Ideal.Quotient.mk 𝔭 b)) =
      Polynomial.aeval ((RatFunc.X : RatFunc (ZMod p))⁻¹) (e' p j 𝔭 e m hej hgen (Ideal.Quotient.mk _ b')) *
        RatFunc.X ^ (m * n) := by
    rw [aeval_e', ← ρ₀_apply, ρ₀'_mul_pow p j 𝔭 e m hej b b' n hb]
  have := congrArg (Φ p κ) h0
  rwa [Φ_aeval_X, map_mul, map_pow, Φ_aeval_Xinv, Φ_X] at this

end MidLift
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry"

end TensorAdapt
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt"

p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace BranchData

open AlgebraicCurve AlgebraicCurve.CurveModel AlgebraicCurve.TwoChartIntegralModel TensorAdapt

variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [Algebra (ZMod p) κ]
  {F : Type} [Field F] (j : F) [Fact (j ≠ 0)]
  (𝔭 : Ideal ↥(chartAlgFin ℤ F j)) (e : (↥(chartAlgFin ℤ F j) ⧸ 𝔭) ≃+* (ZMod p)[X]) (m : ℕ) (hm : 0 < m)
  (hej : e (Ideal.Quotient.mk 𝔭 (jChartFin ℤ F j)) = Polynomial.X ^ m)
  (hgen : ∃ (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ) (b : ↥(chartAlgFin ℤ F j)),
    (b : F) = (b' : F) * j ^ n ∧ e (Ideal.Quotient.mk 𝔭 b) * Polynomial.X = Polynomial.X ^ (m * n))

scoped instance factX : Fact ((RatFunc.X : RatFunc κ) ≠ 0) := ⟨RatFunc.X_ne_zero⟩

private abbrev _root_.BranchData.θFin : κ ⊗[ℤ] ↥(chartAlgFin ℤ F j) →ₐ[κ] ↥(chartRing κ ({RatFunc.X} : Set (RatFunc κ))) :=
  TensorAdapt.θ p κ (Ideal.Quotient.mk 𝔭) e (RatFunc.X : RatFunc κ) (hchart_X κ)

p2m_export "BranchData" "θFin"

private abbrev _root_.BranchData.θInf : κ ⊗[ℤ] ↥(chartAlgInf ℤ F j) →ₐ[κ] ↥(chartRing κ ({(RatFunc.X : RatFunc κ)⁻¹} : Set (RatFunc κ))) :=
  TensorAdapt.θ p κ (Ideal.Quotient.mk (RingHom.ker (ρ₀' p j 𝔭 e m hej))) (e' p j 𝔭 e m hej hgen)
    ((RatFunc.X : RatFunc κ)⁻¹) (mem_chartRing_Xinv_iff κ)

p2m_export "BranchData" "θInf"
theorem θFin_surjective : Function.Surjective (θFin p κ j 𝔭 e) :=
  θ_surjective p κ _ e _ (hchart_X κ) Ideal.Quotient.mk_surjective

theorem θInf_surjective : Function.Surjective (θInf p κ j 𝔭 e m hej hgen) :=
  θ_surjective p κ _ _ _ (mem_chartRing_Xinv_iff κ) Ideal.Quotient.mk_surjective

theorem coe_θFin_tmul (b : ↥(chartAlgFin ℤ F j)) :
    (θFin p κ j 𝔭 e ((1 : κ) ⊗ₜ[ℤ] b) : RatFunc κ) =
      Polynomial.aeval (RatFunc.X : RatFunc κ) ((e (Ideal.Quotient.mk 𝔭 b)).map (algebraMap (ZMod p) κ)) :=
  coe_θ_tmul p κ _ e _ (hchart_X κ) b

theorem coe_θInf_tmul (b' : ↥(chartAlgInf ℤ F j)) :
    (θInf p κ j 𝔭 e m hej hgen ((1 : κ) ⊗ₜ[ℤ] b') : RatFunc κ) =
      Polynomial.aeval ((RatFunc.X : RatFunc κ)⁻¹)
        ((e' p j 𝔭 e m hej hgen (Ideal.Quotient.mk _ b')).map (algebraMap (ZMod p) κ)) :=
  coe_θ_tmul p κ _ _ _ (mem_chartRing_Xinv_iff κ) b'

include hej in
theorem hj : ((θFin p κ j 𝔭 e ((1 : κ) ⊗ₜ[ℤ] jChartFin ℤ F j)) : RatFunc κ) = RatFunc.X ^ m := by
  rw [coe_θFin_tmul, hej, Polynomial.map_pow, Polynomial.map_X, map_pow, Polynomial.aeval_X]

theorem hjInv : ((θInf p κ j 𝔭 e m hej hgen ((1 : κ) ⊗ₜ[ℤ] jInvChartInf ℤ F j)) : RatFunc κ) = (RatFunc.X)⁻¹ ^ m := by
  rw [coe_θInf_tmul, e'_jInv, Polynomial.map_pow, Polynomial.map_X, map_pow, Polynomial.aeval_X]

theorem hcompat (b : ↥(chartAlgFin ℤ F j)) (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ) (hb : (b : F) = (b' : F) * j ^ n) :
    ((θFin p κ j 𝔭 e ((1 : κ) ⊗ₜ[ℤ] b)) : RatFunc κ) =
      ((θInf p κ j 𝔭 e m hej hgen ((1 : κ) ⊗ₜ[ℤ] b')) : RatFunc κ) * RatFunc.X ^ (m * n) := by
  rw [coe_θFin_tmul, coe_θInf_tmul]
  exact compat p j 𝔭 e m hej hgen κ b b' n hb

private def _root_.BranchData.datum : GLUECI.GlueDatum ℤ F j κ (RatFunc.X : RatFunc κ) :=
  GLUECI.datum (m := m) (θFin p κ j 𝔭 e) (θInf p κ j 𝔭 e m hej hgen) hm (hj p κ j 𝔭 e m hej)
    (hcompat p κ j 𝔭 e m hej hgen) (hjInv p κ j 𝔭 e m hej hgen)
    (θFin_surjective p κ j 𝔭 e) (θInf_surjective p κ j 𝔭 e m hej hgen)

p2m_export "BranchData" "datum"
theorem datum_m : (datum p κ j 𝔭 e m hm hej hgen).m = m := rfl

theorem comap_comm_map_includeRight {A : Type} [CommRing A] (I : Ideal A) :
    (I.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A))).comap
        (Algebra.TensorProduct.comm ℤ A κ).toRingHom =
      I.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have hx' : x = (Algebra.TensorProduct.comm ℤ A κ).symm ((Algebra.TensorProduct.comm ℤ A κ) x) :=
      ((Algebra.TensorProduct.comm ℤ A κ).symm_apply_apply x).symm
    rw [hx']
    have hsub : I.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A)) ≤
        (I.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ))).comap
          ((Algebra.TensorProduct.comm ℤ A κ).symm : κ ⊗[ℤ] A →ₐ[ℤ] A ⊗[ℤ] κ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have : ((Algebra.TensorProduct.comm ℤ A κ).symm : κ ⊗[ℤ] A →ₐ[ℤ] A ⊗[ℤ] κ)
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A) a) =
          Algebra.TensorProduct.includeLeftRingHom a := by
        simp [Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [this]
      exact Ideal.mem_map_of_mem _ ha
    exact hsub hx
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : (Algebra.TensorProduct.comm ℤ A κ).toRingHom (Algebra.TensorProduct.includeLeftRingHom a) =
        Algebra.TensorProduct.includeRight (R := ℤ) (A := κ) (B := A) a := by
      simp [Algebra.TensorProduct.includeLeftRingHom_apply]
    rw [this]
    exact Ideal.mem_map_of_mem _ ha

theorem ker_θFin_datum :
    RingHom.ker (datum p κ j 𝔭 e m hm hej hgen).θFin =
      𝔭.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(chartAlgFin ℤ F j)) (B := κ)) := by
  show RingHom.ker (GLUECI.θF (θFin p κ j 𝔭 e)) = _
  rw [GLUECI.ker_θF]
  have hk := ker_θ p κ (Ideal.Quotient.mk 𝔭) e (RatFunc.X : RatFunc κ) (hinj_X κ) (hchart_X κ) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hk
  rw [← RingHom.comap_ker]
  erw [hk]
  try exact comap_comm_map_includeRight κ 𝔭

theorem ker_θInf_datum :
    RingHom.ker (datum p κ j 𝔭 e m hm hej hgen).θInf =
      (RingHom.ker (ρ₀' p j 𝔭 e m hej)).map
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(chartAlgInf ℤ F j)) (B := κ)) := by
  show RingHom.ker (GLUECI.θI (θInf p κ j 𝔭 e m hej hgen)) = _
  rw [GLUECI.ker_θI]
  have hk := ker_θ p κ (Ideal.Quotient.mk (RingHom.ker (ρ₀' p j 𝔭 e m hej))) (e' p j 𝔭 e m hej hgen)
    ((RatFunc.X : RatFunc κ)⁻¹) (aeval_Xinv_injective κ) (mem_chartRing_Xinv_iff κ) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hk
  rw [← RingHom.comap_ker]
  erw [hk]
  try exact comap_comm_map_includeRight κ (RingHom.ker (ρ₀' p j 𝔭 e m hej))

theorem tmul_mem_ker_θFin_iff (a : ↥(chartAlgFin ℤ F j)) :
    a ⊗ₜ[ℤ] (1 : κ) ∈ RingHom.ker (datum p κ j 𝔭 e m hm hej hgen).θFin ↔ a ∈ 𝔭 := by
  rw [RingHom.mem_ker]
  show GLUECI.θF (θFin p κ j 𝔭 e) (a ⊗ₜ[ℤ] (1 : κ)) = 0 ↔ _
  rw [GLUECI.θF_tmul, ← ZeroMemClass.coe_eq_zero, coe_θFin_tmul,
    map_eq_zero_iff _ (hinj_X κ), Polynomial.map_eq_zero_iff (algebraMap (ZMod p) κ).injective,
    map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]

theorem tmul_mem_ker_θInf_iff (a' : ↥(chartAlgInf ℤ F j)) :
    a' ⊗ₜ[ℤ] (1 : κ) ∈ RingHom.ker (datum p κ j 𝔭 e m hm hej hgen).θInf ↔ a' ∈ RingHom.ker (ρ₀' p j 𝔭 e m hej) := by
  rw [RingHom.mem_ker, RingHom.mem_ker]
  show GLUECI.θI (θInf p κ j 𝔭 e m hej hgen) (a' ⊗ₜ[ℤ] (1 : κ)) = 0 ↔ ρ₀' p j 𝔭 e m hej a' = 0
  rw [← RingHom.mem_ker (f := ρ₀' p j 𝔭 e m hej)]
  rw [GLUECI.θI_tmul, ← ZeroMemClass.coe_eq_zero, coe_θInf_tmul,
    map_eq_zero_iff _ (aeval_Xinv_injective κ), Polynomial.map_eq_zero_iff (algebraMap (ZMod p) κ).injective,
    map_eq_zero_iff _ (e' p j 𝔭 e m hej hgen).injective, Ideal.Quotient.eq_zero_iff_mem]

theorem mem_ker_ρ₀'_iff_mem_nonunits (W : ValuationSubring F)
    (h𝔭 : ∀ a : ↥(chartAlgFin ℤ F j), a ∈ 𝔭 ↔ ((a : F) ∈ W.nonunits))
    (hjW : j ∈ W) (hjW' : j⁻¹ ∈ W) (a' : ↥(chartAlgInf ℤ F j)) :
    a' ∈ RingHom.ker (ρ₀' p j 𝔭 e m hej) ↔ ((a' : F) ∈ W.nonunits) := by

  letI := (TwoChartIntegralModel.inclFin ℤ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤ F j
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ :=
    IsLocalization.surj (Submonoid.powers (jChartFin ℤ F j)) (TwoChartIntegralModel.inclInf ℤ F j a')
  have hbF : (b : F) = (a' : F) * j ^ n := by
    have := congrArg (fun z : ↥(chartAlgMid ℤ F j) => (z : F)) hb
    simpa only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, TwoChartIntegralModel.coe_chartIncl, coe_jChartFin] using this.symm
  rw [mem_ker_ρ₀'_iff p j 𝔭 e m hej a' n b hbF, h𝔭, hbF, ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff, map_mul, map_pow]

  have hj0 : W.valuation j ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact Fact.out
  have hv1 : W.valuation j = 1 := by
    apply le_antisymm ((W.valuation_le_one_iff j).mpr hjW)
    have h := (W.valuation_le_one_iff j⁻¹).mpr hjW'
    rwa [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hj0)] at h
  rw [hv1, one_pow, mul_one]

def θpoly : ↥(chartAlgFin ℤ F j) ⊗[ℤ] κ →+* κ[X] :=
  (θP p κ (Ideal.Quotient.mk 𝔭) e).comp (Algebra.TensorProduct.comm ℤ ↥(chartAlgFin ℤ F j) κ).toRingHom

omit [Fact (j ≠ 0)] in
theorem θpoly_tmul (b : ↥(chartAlgFin ℤ F j)) (c : κ) :
    θpoly p κ j 𝔭 e (b ⊗ₜ[ℤ] c) = Polynomial.C c * (e (Ideal.Quotient.mk 𝔭 b)).map (algebraMap (ZMod p) κ) := by
  show θP p κ (Ideal.Quotient.mk 𝔭) e ((Algebra.TensorProduct.comm ℤ ↥(chartAlgFin ℤ F j) κ) (b ⊗ₜ[ℤ] c)) = _
  rw [Algebra.TensorProduct.comm_tmul, θP_tmul]

omit [Fact (j ≠ 0)] in
theorem θpoly_tmul_one (b : ↥(chartAlgFin ℤ F j)) :
    θpoly p κ j 𝔭 e (b ⊗ₜ[ℤ] (1 : κ)) = (e (Ideal.Quotient.mk 𝔭 b)).map (algebraMap (ZMod p) κ) := by
  rw [θpoly_tmul, Polynomial.C_1, one_mul]

omit [Fact (j ≠ 0)] in
theorem θpoly_surjective : Function.Surjective (θpoly p κ j 𝔭 e) :=
  (θP_surjective p κ _ e Ideal.Quotient.mk_surjective).comp (Algebra.TensorProduct.comm ℤ _ κ).surjective

omit [Fact (j ≠ 0)] in
theorem ker_θpoly :
    RingHom.ker (θpoly p κ j 𝔭 e) =
      𝔭.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(chartAlgFin ℤ F j)) (B := κ)) := by
  have hk := ker_θP p κ (Ideal.Quotient.mk 𝔭) e Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hk
  rw [θpoly, ← RingHom.comap_ker]
  erw [hk]
  try exact comap_comm_map_includeRight κ 𝔭

theorem coe_datum_θFin (z : ↥(chartAlgFin ℤ F j) ⊗[ℤ] κ) :
    ((datum p κ j 𝔭 e m hm hej hgen).θFin z : RatFunc κ) = Polynomial.aeval (RatFunc.X : RatFunc κ) (θpoly p κ j 𝔭 e z) := by
  show ((θFin p κ j 𝔭 e ((Algebra.TensorProduct.comm ℤ ↥(chartAlgFin ℤ F j) κ) z)) : RatFunc κ) = _
  exact (Θ_eq_aeval_θP p κ (Ideal.Quotient.mk 𝔭) e (RatFunc.X : RatFunc κ) _)

end BranchData
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry ModularCurve AlgebraicCurve"
p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace TwoLinesAsm

section Generic

theorem map_le_or_map_le_of_minimalPrimes {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    {κ : Type*} [Field κ] [Algebra R κ] (r : R) (hr : algebraMap R κ r = 0) (I₁ I₂ : Ideal A)
    (hmin : ∀ 𝔭 : Ideal A, 𝔭 ∈ (Ideal.span {algebraMap R A r}).minimalPrimes → 𝔭 = I₁ ∨ 𝔭 = I₂)
    (𝔮 : PrimeSpectrum (A ⊗[R] κ)) :
    I₁.map (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] κ) ≤ 𝔮.asIdeal ∨
      I₂.map (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] κ) ≤ 𝔮.asIdeal := by
  have hr' : Ideal.span {algebraMap R A r} ≤
      𝔮.asIdeal.comap (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] κ) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    have h0 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap R A r) : A ⊗[R] κ) = 0 := by
      rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, hr, TensorProduct.tmul_zero]
    rw [h0]
    exact Ideal.zero_mem _
  obtain ⟨𝔭, h𝔭, h𝔭le⟩ := Ideal.exists_minimalPrimes_le hr'
  rcases hmin 𝔭 h𝔭 with rfl | rfl
  · exact Or.inl (Ideal.map_le_iff_le_comap.mpr h𝔭le)
  · exact Or.inr (Ideal.map_le_iff_le_comap.mpr h𝔭le)

theorem not_le_of_mem_minimalPrimes {A : Type*} [CommRing A] {I 𝔭 𝔭' : Ideal A}
    (h : 𝔭 ∈ I.minimalPrimes) (h' : 𝔭' ∈ I.minimalPrimes) (hne : 𝔭 ≠ 𝔭') : ¬ 𝔭' ≤ 𝔭 :=
  fun hle => hne (le_antisymm (h.2 h'.1 hle) hle)

theorem ne_of_ncard_minimalPrimes {A : Type*} [CommRing A] {I I₁ I₂ : Ideal A}
    (hmin : ∀ 𝔭 : Ideal A, 𝔭 ∈ I.minimalPrimes → 𝔭 = I₁ ∨ 𝔭 = I₂) (hcard : I.minimalPrimes.ncard = 2) : I₁ ≠ I₂ := by
  intro heq
  have hsub : I.minimalPrimes ⊆ {I₁} := fun 𝔭 h𝔭 => by
    rcases hmin 𝔭 h𝔭 with rfl | rfl
    · rfl
    · exact heq.symm
  have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [hcard, Set.ncard_singleton] at this
  omega

theorem exists_pair_of_ncard_eq_two {α : Type*} {s : Set α} {P Q : α → Prop} (hcard : s.ncard = 2)
    (hmem : ∀ x ∈ s, P x ∨ Q x) (hP : ∀ x y, P x → P y → x = y) (hQ : ∀ x y, Q x → Q y → x = y) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧ P x ∧ Q y := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.mp hcard
  have ha : a ∈ ({a, b} : Set α) := Set.mem_insert _ _
  have hb : b ∈ ({a, b} : Set α) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  rcases hmem a ha with hPa | hQa <;> rcases hmem b hb with hPb | hQb
  · exact absurd (hP a b hPa hPb) hab
  · exact ⟨a, b, ha, hb, hab, hPa, hQb⟩
  · exact ⟨b, a, hb, ha, hab.symm, hPb, hQa⟩
  · exact absurd (hQ a b hQa hQb) hab

variable {X : Scheme.{u}}

theorem transport_singleton {Y Y' : Scheme.{u}} (f : Y ⟶ X) (g : Y' ⟶ X) [IsClosedImmersion f]
    [IsClosedImmersion g] (hfg : Set.range f.base = Set.range g.base) (L : Set X)
    (h : ∃ y : closedPoints Y', L ∩ Set.range g.base = {g.base y.1}) :
    ∃ x : closedPoints Y, L ∩ Set.range f.base = {f.base x.1} := by
  obtain ⟨⟨y, hy⟩, hL⟩ := h
  have hmem : g.base y ∈ Set.range f.base := by
    rw [hfg]; exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  have hclosed_pt : IsClosed ({g.base y} : Set X) := by
    rw [← Set.image_singleton]
    exact g.isClosedEmbedding.isClosedMap _ ((mem_closedPoints_iff).mp hy)
  have hxclosed : IsClosed ({x} : Set Y) := by
    have : ({x} : Set Y) = f.base ⁻¹' {g.base y} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hx
      · intro hz; exact f.isClosedEmbedding.injective (hz.trans hx.symm)
    rw [this]
    exact hclosed_pt.preimage f.continuous
  refine ⟨⟨x, (mem_closedPoints_iff).mpr hxclosed⟩, ?_⟩
  rw [hfg, hL, hx]

theorem range_iso_hom_comp {Y Y' : Scheme.{u}} (e : Y' ≅ Y) (c : Y ⟶ X) :
    Set.range (e.hom ≫ c).base = Set.range c.base := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.hom.base y, (Scheme.Hom.comp_apply e.hom c y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    have hy : e.hom.base (e.inv.base y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    rw [Scheme.Hom.comp_apply, hy]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

section Branch

p2m_open "AlgebraicCurve.TwoChartIntegralModel"

theorem branch (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [Algebra (ZMod p) κ]
    {F : Type} [Field F] (j : F) [Fact (j ≠ 0)]
    (𝔭 : Ideal ↥(chartAlgFin ℤ F j)) (e : (↥(chartAlgFin ℤ F j) ⧸ 𝔭) ≃+* (ZMod p)[X]) (m : ℕ) (hm : 0 < m)
    (hej : e (Ideal.Quotient.mk 𝔭 (jChartFin ℤ F j)) = Polynomial.X ^ m)
    (hgen : ∃ (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ) (b : ↥(chartAlgFin ℤ F j)),
      (b : F) = (b' : F) * j ^ n ∧ e (Ideal.Quotient.mk 𝔭 b) * Polynomial.X = Polynomial.X ^ (m * n))
    (W : ValuationSubring F) (h𝔭 : ∀ a : ↥(chartAlgFin ℤ F j), a ∈ 𝔭 ↔ ((a : F) ∈ W.nonunits))
    (hjW : j ∈ W) (hjW' : j⁻¹ ∈ W) :
    ∃ (D : GLUECI.GlueDatum ℤ F j κ (RatFunc.X : RatFunc κ)) (𝔮 : Ideal ↥(chartAlgInf ℤ F j)),
      D.m = m ∧
      D.IFin = 𝔭.map (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin ℤ F j) →+* ↥(chartAlgFin ℤ F j) ⊗[ℤ] κ) ∧
      (∀ a : ↥(chartAlgFin ℤ F j), a ⊗ₜ[ℤ] (1 : κ) ∈ D.IFin ↔ a ∈ 𝔭) ∧
      (∀ a : ↥(chartAlgInf ℤ F j), a ∈ 𝔮 ↔ ((a : F) ∈ W.nonunits)) ∧
      D.IInf = 𝔮.map (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf ℤ F j) →+* ↥(chartAlgInf ℤ F j) ⊗[ℤ] κ) :=
  ⟨BranchData.datum p κ j 𝔭 e m hm hej hgen, RingHom.ker (TensorAdapt.ρ₀' p j 𝔭 e m hej), rfl,
    BranchData.ker_θFin_datum p κ j 𝔭 e m hm hej hgen,
    BranchData.tmul_mem_ker_θFin_iff p κ j 𝔭 e m hm hej hgen,
    BranchData.mem_ker_ρ₀'_iff_mem_nonunits p j 𝔭 e m hej W h𝔭 hjW hjW',
    BranchData.ker_θInf_datum p κ j 𝔭 e m hm hej hgen⟩

end Branch
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

section Cert

p2m_open "AlgebraicCurve.TwoChartIntegralModel"

set_option maxHeartbeats 1600000 in

structure Cert (p : ℕ) [Fact p.Prime] [NeZero p] (κ : Type) [Field κ] [Algebra (ZMod p) κ]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p)) where
  𝔭₀ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
  𝔭₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
  h𝔭₀ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔭₀ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
  h𝔭₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
  h𝔭₀min : 𝔭₀ ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes
  h𝔭₁min : 𝔭₁ ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes
  hne𝔭 : 𝔭₀ ≠ 𝔭₁
  hminFin : ∀ 𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes → 𝔭 = 𝔭₀ ∨ 𝔭 = 𝔭₁
  e₀ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₀) ≃+* Polynomial (ZMod p)
  e₁ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+* Polynomial (ZMod p)
  he₀j : e₀ (Ideal.Quotient.mk 𝔭₀ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X
  he₀jp : e₀ (Ideal.Quotient.mk 𝔭₀ jp) = Polynomial.X ^ p
  he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = Polynomial.X
  he₁j : e₁ (Ideal.Quotient.mk 𝔭₁ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X ^ p
  Dinf : GLUECI.GlueDatum ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ (RatFunc.X : RatFunc κ)
  Dzero : GLUECI.GlueDatum ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ (RatFunc.X : RatFunc κ)
  hm₀ : Dinf.m = 1
  hm₁ : Dzero.m = p
  hKF₀ : Dinf.IFin = 𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)
  hKF₁ : Dzero.IFin = 𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)
  hA₀ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ⊗ₜ[ℤ] (1 : κ) ∈ Dinf.IFin ↔ a ∈ 𝔭₀
  hA₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ⊗ₜ[ℤ] (1 : κ) ∈ Dzero.IFin ↔ a ∈ 𝔭₁
  𝔮₀ : Ideal ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
  𝔮₁ : Ideal ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
  h𝔮₀ : ∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔮₀ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
  h𝔮₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔮₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
  hKI₀ : Dinf.IInf = 𝔮₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)
  hKI₁ : Dzero.IInf = 𝔮₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)
  hminInf : ∀ 𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes → 𝔭 = 𝔮₀ ∨ 𝔭 = 𝔮₁

theorem nonempty_cert
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits)
    (κ : Type) [Field κ] [Algebra (ZMod p) κ] :
    Nonempty (Cert p κ jp W₀ W₁) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos

  have hXp : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  have hjW₀ : ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ∈ W₀ ∧ ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p))⁻¹ ∈ W₀ := by
    simpa only [Polynomial.eval₂_X, Matrix.cons_val_zero] using hgen 0 Polynomial.X hXp
  have hjW₁ : ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ∈ W₁ ∧ ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p))⁻¹ ∈ W₁ := by
    simpa only [Polynomial.eval₂_X, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] using
      hgen 1 Polynomial.X hXp

  have hM := ModularCurve.DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair p jp hjp W₀ W₁ hp₀ hp₁
    hne hgen hcomplete ht
  have hM' := ModularCurve.DRModel.mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair p jp hjp W₀ W₁ hp₀ hp₁
    hne hgen hcomplete ht

  obtain ⟨-, hcardFin, -, -⟩ :=
    ModularCurve.DRModel.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int p
  obtain ⟨𝔭₀, 𝔭₁, h𝔭₀min, h𝔭₁min, hne𝔭, h𝔭₀, h𝔭₁⟩ := exists_pair_of_ncard_eq_two hcardFin
    (fun 𝔭 h => (hM 𝔭).mp h)
    (fun x y hx hy => Ideal.ext fun a => (hx a).trans (hy a).symm)
    (fun x y hx hy => Ideal.ext fun a => (hx a).trans (hy a).symm)

  obtain ⟨hS1₀, hS1₁⟩ := ModularCurve.DRModel.exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
    p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁
  obtain ⟨e₀, he₀j, he₀jp⟩ := hS1₀ 𝔭₀ h𝔭₀
  obtain ⟨e₁, he₁jp, he₁j⟩ := hS1₁ 𝔭₁ h𝔭₁

  obtain ⟨hgen₁, -⟩ :=
    ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair p jp hjp W₀ W₁
      hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ 𝔭₁ h𝔭₁ e₁ he₁jp he₁j
  have hej₀ : e₀ (Ideal.Quotient.mk 𝔭₀ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X ^ 1 := by
    rw [pow_one]; exact he₀j
  have hgen₀ : ∃ (b' : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (n : ℕ) (b : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))),
      (b : ↥(modularFunctionFieldFull p)) = (b' : ↥(modularFunctionFieldFull p)) * ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ^ n ∧
        e₀ (Ideal.Quotient.mk 𝔭₀ b) * Polynomial.X = Polynomial.X ^ (1 * n) := by
    refine ⟨jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p), 1, 1, ?_, ?_⟩
    · rw [OneMemClass.coe_one, coe_jInvChartInf, pow_one, inv_mul_cancel₀ (j_ne_zero (IgusaScheme.jFull p))]
    · rw [map_one, map_one, one_mul, one_mul, pow_one]

  obtain ⟨Dinf, 𝔮₀, hm₀, hKF₀, hA₀, h𝔮₀, hKI₀⟩ :=
    branch p κ (IgusaScheme.jFull p) 𝔭₀ e₀ 1 one_pos hej₀ hgen₀ W₀ h𝔭₀ hjW₀.1 hjW₀.2
  obtain ⟨Dzero, 𝔮₁, hm₁, hKF₁, hA₁, h𝔮₁, hKI₁⟩ :=
    branch p κ (IgusaScheme.jFull p) 𝔭₁ e₁ p hp he₁j hgen₁ W₁ h𝔭₁ hjW₁.1 hjW₁.2
  have hminFin : ∀ 𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes → 𝔭 = 𝔭₀ ∨ 𝔭 = 𝔭₁ := by
    intro 𝔭 h𝔭
    rcases (hM 𝔭).mp h𝔭 with h | h
    · exact Or.inl (Ideal.ext fun a => (h a).trans (h𝔭₀ a).symm)
    · exact Or.inr (Ideal.ext fun a => (h a).trans (h𝔭₁ a).symm)
  have hminInf : ∀ 𝔭 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes → 𝔭 = 𝔮₀ ∨ 𝔭 = 𝔮₁ := by
    intro 𝔭 h𝔭
    rcases (hM' 𝔭).mp h𝔭 with h | h
    · exact Or.inl (Ideal.ext fun a => (h a).trans (h𝔮₀ a).symm)
    · exact Or.inr (Ideal.ext fun a => (h a).trans (h𝔮₁ a).symm)
  exact ⟨{ 𝔭₀ := 𝔭₀, 𝔭₁ := 𝔭₁, h𝔭₀ := h𝔭₀, h𝔭₁ := h𝔭₁, h𝔭₀min := h𝔭₀min, h𝔭₁min := h𝔭₁min, hne𝔭 := hne𝔭,
            hminFin := hminFin, e₀ := e₀, e₁ := e₁, he₀j := he₀j, he₀jp := he₀jp, he₁jp := he₁jp, he₁j := he₁j,
            Dinf := Dinf, Dzero := Dzero, hm₀ := hm₀, hm₁ := hm₁, hKF₀ := hKF₀, hKF₁ := hKF₁, hA₀ := hA₀, hA₁ := hA₁,
            𝔮₀ := 𝔮₀, 𝔮₁ := 𝔮₁, h𝔮₀ := h𝔮₀, h𝔮₁ := h𝔮₁, hKI₀ := hKI₀, hKI₁ := hKI₁, hminInf := hminInf }⟩

variable {p : ℕ} [Fact p.Prime] [NeZero p] {κ : Type} [Field κ] [CharP κ p] [Algebra (ZMod p) κ]
  {jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))} {W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p)} (𝒞 : Cert p κ jp W₀ W₁)

theorem Cert.cover : ∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
    x ∈ Set.range (GLUECI.es 𝒞.Dinf).base ∨ x ∈ Set.range (GLUECI.es 𝒞.Dzero).base := by
  have hpκ : algebraMap ℤ κ (p : ℤ) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero κ p
  have hspanFin : (algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (p : ℤ)) = ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by rw [map_natCast]
  have hspanInf : (algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (p : ℤ)) = ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by rw [map_natCast]
  have hcovFin : ∀ 𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ), 𝒞.Dinf.IFin ≤ 𝔮.asIdeal ∨ 𝒞.Dzero.IFin ≤ 𝔮.asIdeal := by
    intro 𝔮
    rw [𝒞.hKF₀, 𝒞.hKF₁]
    exact map_le_or_map_le_of_minimalPrimes (p : ℤ) hpκ 𝒞.𝔭₀ 𝒞.𝔭₁ (by rw [hspanFin]; exact 𝒞.hminFin) 𝔮
  have hcovInf : ∀ 𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ), 𝒞.Dinf.IInf ≤ 𝔮.asIdeal ∨ 𝒞.Dzero.IInf ≤ 𝔮.asIdeal := by
    intro 𝔮
    rw [𝒞.hKI₀, 𝒞.hKI₁]
    exact map_le_or_map_le_of_minimalPrimes (p : ℤ) hpκ 𝒞.𝔮₀ 𝒞.𝔮₁ (by rw [hspanInf]; exact 𝒞.hminInf) 𝔮
  exact GLUECI.forall_mem_range_es_or 𝒞.Dinf 𝒞.Dzero hcovFin hcovInf

theorem Cert.exists_mem_inf_not_mem_zero : ∃ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
    x ∈ Set.range (GLUECI.es 𝒞.Dinf).base ∧ x ∉ Set.range (GLUECI.es 𝒞.Dzero).base := by
  have hnle : ¬ 𝒞.𝔭₁ ≤ 𝒞.𝔭₀ := not_le_of_mem_minimalPrimes 𝒞.h𝔭₀min 𝒞.h𝔭₁min 𝒞.hne𝔭
  refine ⟨(GLUECI.gFin 𝒞.Dinf).base (GLUECI.genFin 𝒞.Dinf), GLUECI.gFin_genFin_mem_range_es 𝒞.Dinf, fun h => ?_⟩
  have hle : 𝒞.Dzero.IFin ≤ 𝒞.Dinf.IFin := GLUECI.IFin_le_of_genFin_mem_range 𝒞.Dinf 𝒞.Dzero h
  obtain ⟨a, ha₁, ha₀⟩ := SetLike.not_le_iff_exists.mp hnle
  exact ha₀ ((𝒞.hA₀ a).mp (hle ((𝒞.hA₁ a).mpr ha₁)))

theorem Cert.exists_mem_zero_not_mem_inf : ∃ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
    x ∈ Set.range (GLUECI.es 𝒞.Dzero).base ∧ x ∉ Set.range (GLUECI.es 𝒞.Dinf).base := by
  have hnle : ¬ 𝒞.𝔭₀ ≤ 𝒞.𝔭₁ := not_le_of_mem_minimalPrimes 𝒞.h𝔭₁min 𝒞.h𝔭₀min 𝒞.hne𝔭.symm
  refine ⟨(GLUECI.gFin 𝒞.Dzero).base (GLUECI.genFin 𝒞.Dzero), GLUECI.gFin_genFin_mem_range_es 𝒞.Dzero, fun h => ?_⟩
  have hle : 𝒞.Dinf.IFin ≤ 𝒞.Dzero.IFin := GLUECI.IFin_le_of_genFin_mem_range 𝒞.Dzero 𝒞.Dinf h
  obtain ⟨a, ha₀, ha₁⟩ := SetLike.not_le_iff_exists.mp hnle
  exact ha₁ ((𝒞.hA₁ a).mp (hle ((𝒞.hA₀ a).mpr ha₀)))

theorem Cert.range_ne : Set.range (GLUECI.es 𝒞.Dinf).base ≠ Set.range (GLUECI.es 𝒞.Dzero).base := by
  intro h
  obtain ⟨x, hx, hx'⟩ := 𝒞.exists_mem_inf_not_mem_zero
  exact hx' (h ▸ hx)

end Cert
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

namespace FbPlus

section Topology

open Set Topology

variable {X : Type*} [TopologicalSpace X]

theorem irred_subset_or {S Z₁ Z₂ : Set X} (hS : IsIrreducible S) (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : S ⊆ Z₁ ∪ Z₂) : S ⊆ Z₁ ∨ S ⊆ Z₂ :=
  (isPreirreducible_iff_isClosed_union_isClosed.mp hS.isPreirreducible) Z₁ Z₂ h₁ h₂ h

theorem pair_eq_of_irreducible_closed_covers {A B A' B' : Set X}
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hAc : IsClosed A) (hBc : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    (hA' : IsIrreducible A') (hB' : IsIrreducible B') (hA'c : IsClosed A') (hB'c : IsClosed B')
    (hcov' : ∀ x, x ∈ A' ∨ x ∈ B')
    (hAB' : ¬ A' ⊆ B') (hBA' : ¬ B' ⊆ A') :
    (A = A' ∧ B = B') ∨ (A = B' ∧ B = A') := by
  have cov : ∀ S : Set X, S ⊆ A ∪ B := fun S x _ => hcov x
  have cov' : ∀ S : Set X, S ⊆ A' ∪ B' := fun S x _ => hcov' x
  have hA_or := irred_subset_or hA hA'c hB'c (cov' A)
  have hB_or := irred_subset_or hB hA'c hB'c (cov' B)
  have hA'_or := irred_subset_or hA' hAc hBc (cov A')
  have hB'_or := irred_subset_or hB' hAc hBc (cov B')

  rcases hA'_or with hA'A | hA'B
  ·
    have hAA' : A ⊆ A' := by
      rcases hA_or with h | h
      · exact h
      · exact absurd (hA'A.trans h) hAB'
    have eA : A = A' := hAA'.antisymm hA'A
    refine Or.inl ⟨eA, ?_⟩
    rcases hB'_or with hB'A | hB'B
    · exact absurd (hB'A.trans hAA') hBA'
    · refine (?_ : B ⊆ B').antisymm hB'B
      rcases hB_or with h | h
      ·
        exfalso; apply hBA'
        intro x hx
        rcases hcov x with hxA | hxB
        · exact hAA' hxA
        · exact h hxB
      · exact h
  ·
    have hBA'' : B ⊆ A' := by
      rcases hB_or with h | h
      · exact h
      · exact absurd (hA'B.trans h) hAB'
    have eB : B = A' := hBA''.antisymm hA'B
    refine Or.inr ⟨?_, eB⟩
    rcases hB'_or with hB'A | hB'B
    · refine (?_ : A ⊆ B').antisymm hB'A
      rcases hA_or with h | h
      · exfalso; apply hBA'
        intro x hx
        rcases hcov x with hxA | hxB
        · exact h hxA
        · exact hBA'' hxB
      · exact h
    · exact absurd (hB'B.trans hBA'') hBA'

theorem mem_cover_eq_or {A B A' B' S : Set X}
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hAc : IsClosed A) (hBc : IsClosed B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    (hA' : IsIrreducible A') (hB' : IsIrreducible B') (hA'c : IsClosed A') (hB'c : IsClosed B')
    (hcov' : ∀ x, x ∈ A' ∨ x ∈ B')
    (hAB' : ¬ A' ⊆ B') (hBA' : ¬ B' ⊆ A') (hS : S = A ∨ S = B) :
    S = A' ∨ S = B' := by
  rcases pair_eq_of_irreducible_closed_covers hA hB hAc hBc hcov hA' hB' hA'c hB'c hcov' hAB' hBA' with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hS
  · exact hS.symm

end Topology
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

section SchemeTransport

open Set Topology

variable {X : Scheme.{u}}

theorem isClosed_range_of_isClosedImmersion {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] :
    IsClosed (Set.range f.base) :=
  f.isClosedEmbedding.isClosed_range

theorem isIrreducible_range_of_irreducibleSpace {Y : Scheme.{u}} [IrreducibleSpace Y] (f : Y ⟶ X) :
    IsIrreducible (Set.range f.base) := by
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ Y).image f.base f.continuous.continuousOn

theorem transport_singleton {Y Y' : Scheme.{u}} (f : Y ⟶ X) (g : Y' ⟶ X) [IsClosedImmersion f]
    [IsClosedImmersion g] (hfg : Set.range f.base = Set.range g.base) (L : Set X)
    (h : ∃ y : closedPoints Y', L ∩ Set.range g.base = {g.base y.1}) :
    ∃ x : closedPoints Y, L ∩ Set.range f.base = {f.base x.1} := by
  obtain ⟨⟨y, hy⟩, hL⟩ := h
  have hmem : g.base y ∈ Set.range f.base := by
    rw [hfg]; exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  have hclosed_pt : IsClosed ({g.base y} : Set X) := by
    rw [← Set.image_singleton]
    exact g.isClosedEmbedding.isClosedMap _ ((mem_closedPoints_iff).mp hy)
  have hxclosed : IsClosed ({x} : Set Y) := by
    have : ({x} : Set Y) = f.base ⁻¹' {g.base y} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hx
      · intro hz; exact f.isClosedEmbedding.injective (hz.trans hx.symm)
    rw [this]
    exact hclosed_pt.preimage f.continuous
  refine ⟨⟨x, (mem_closedPoints_iff).mpr hxclosed⟩, ?_⟩
  rw [hfg, hL, hx]

end SchemeTransport
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

end FbPlus
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

section BranchA

p2m_open "AlgebraicCurve.TwoChartIntegralModel"

variable {p : ℕ} [Fact p.Prime] [NeZero p] {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (ZMod p) κ]
  {jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))} {W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p)}

theorem Cert.exists_swap_range_comp_eq (𝔛 : DRModelPackage p) (𝒞 : Cert p κ jp W₀ W₁) :
    ∃ swap : Bool,
      Set.range (𝔛.compInf κ).base = Set.range (GLUECI.es (if swap then 𝒞.Dzero else 𝒞.Dinf)).base ∧
      Set.range (𝔛.compZero κ).base = Set.range (GLUECI.es (if swap then 𝒞.Dinf else 𝒞.Dzero)).base := by
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  haveI := GLUECI.isClosedImmersion_es 𝒞.Dinf
  haveI := GLUECI.isClosedImmersion_es 𝒞.Dzero

  obtain ⟨M, e, -⟩ := AlgebraicCurve.CurveModel.exists_curveModel_ratFunc κ
  have hrInf : Set.range (e.hom ≫ GLUECI.es 𝒞.Dinf).base = Set.range (GLUECI.es 𝒞.Dinf).base := range_iso_hom_comp e _
  have hrZero : Set.range (e.hom ≫ GLUECI.es 𝒞.Dzero).base = Set.range (GLUECI.es 𝒞.Dzero).base := range_iso_hom_comp e _
  have hirrInf : IsIrreducible (Set.range (GLUECI.es 𝒞.Dinf).base) :=
    hrInf ▸ FbPlus.isIrreducible_range_of_irreducibleSpace (e.hom ≫ GLUECI.es 𝒞.Dinf)
  have hirrZero : IsIrreducible (Set.range (GLUECI.es 𝒞.Dzero).base) :=
    hrZero ▸ FbPlus.isIrreducible_range_of_irreducibleSpace (e.hom ≫ GLUECI.es 𝒞.Dzero)
  obtain ⟨x, hx, hx'⟩ := 𝒞.exists_mem_inf_not_mem_zero
  obtain ⟨y, hy, hy'⟩ := 𝒞.exists_mem_zero_not_mem_inf
  rcases FbPlus.pair_eq_of_irreducible_closed_covers
      (FbPlus.isIrreducible_range_of_irreducibleSpace (𝔛.compInf κ))
      (FbPlus.isIrreducible_range_of_irreducibleSpace (𝔛.compZero κ))
      (FbPlus.isClosed_range_of_isClosedImmersion (𝔛.compInf κ))
      (FbPlus.isClosed_range_of_isClosedImmersion (𝔛.compZero κ))
      (𝔛.comp_jointly_surjective κ) hirrInf hirrZero
      (FbPlus.isClosed_range_of_isClosedImmersion (GLUECI.es 𝒞.Dinf))
      (FbPlus.isClosed_range_of_isClosedImmersion (GLUECI.es 𝒞.Dzero))
      𝒞.cover (fun h => hx' (h hx)) (fun h => hy' (h hy)) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨false, h₁, h₂⟩
  · exact ⟨true, h₁, h₂⟩

theorem Cert.gFin_mem_range_es_Dinf_iff (𝒞 : Cert p κ jp W₀ W₁) (z : GLUECI.PFin 𝒞.Dinf) :
    (GLUECI.gFin 𝒞.Dinf).base z ∈ Set.range (GLUECI.es 𝒞.Dinf).base ↔
      𝒞.𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤
        ((GLUECI.isoFin 𝒞.Dinf).hom.base z).asIdeal := by
  rw [GLUECI.gFin_mem_range_es_iff, GLUECI.mem_range_φFin_iff, ← 𝒞.hKF₀]
  rfl

theorem Cert.gFin_mem_range_es_Dzero_iff (𝒞 : Cert p κ jp W₀ W₁) (z : GLUECI.PFin 𝒞.Dinf) :
    (GLUECI.gFin 𝒞.Dinf).base z ∈ Set.range (GLUECI.es 𝒞.Dzero).base ↔
      𝒞.𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤
        ((GLUECI.isoFin 𝒞.Dinf).hom.base z).asIdeal := by
  have h := (GLUECI.gFin_mem_range_es_iff 𝒞.Dzero z).trans (GLUECI.mem_range_φFin_iff 𝒞.Dzero z)
  have h2 : RingHom.ker 𝒞.Dzero.θFin =
      𝒞.𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) := 𝒞.hKF₁
  rw [h2] at h
  exact h

set_option maxHeartbeats 1600000 in

theorem Cert.jp_sub_j_pow_mem (𝒞 : Cert p κ jp W₀ W₁) :
    jp - (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ^ p ∈ 𝒞.𝔭₀ ∧ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) - jp ^ p ∈ 𝒞.𝔭₁ := by
  have h0j : 𝒞.e₀ (Ideal.Quotient.mk 𝒞.𝔭₀ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X := 𝒞.he₀j
  have h0jp : 𝒞.e₀ (Ideal.Quotient.mk 𝒞.𝔭₀ jp) = Polynomial.X ^ p := 𝒞.he₀jp
  have h1j : 𝒞.e₁ (Ideal.Quotient.mk 𝒞.𝔭₁ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X ^ p := 𝒞.he₁j
  have h1jp : 𝒞.e₁ (Ideal.Quotient.mk 𝒞.𝔭₁ jp) = Polynomial.X := 𝒞.he₁jp
  constructor
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply 𝒞.e₀.injective
    rw [map_zero, map_sub, map_sub, h0jp, map_pow, map_pow, h0j, sub_self]
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply 𝒞.e₁.injective
    rw [map_zero, map_sub, map_sub, h1j, map_pow, map_pow, h1jp, sub_self]

theorem Cert.map_le_or_map_le (𝒞 : Cert p κ jp W₀ W₁) (𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)) :
    𝒞.𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤ 𝔮.asIdeal ∨
      𝒞.𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤ 𝔮.asIdeal := by
  have hpκ : algebraMap ℤ κ (p : ℤ) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero κ p
  have hspanFin : (algebraMap ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (p : ℤ)) = ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by rw [map_natCast]
  exact map_le_or_map_le_of_minimalPrimes (p : ℤ) hpκ 𝒞.𝔭₀ 𝒞.𝔭₁ (by rw [hspanFin]; exact 𝒞.hminFin) 𝔮

theorem Cert.ker_dichotomy (𝒞 : Cert p κ jp W₀ W₁) {S : Type} [CommRing S] [IsDomain S] [CharP S p]
    (χ : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* S) :
    (𝒞.𝔭₀ ≤ RingHom.ker χ ∨ 𝒞.𝔭₁ ≤ RingHom.ker χ) ∧
    (𝒞.𝔭₀ ≤ RingHom.ker χ → χ jp = χ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ^ p) ∧
    (𝒞.𝔭₁ ≤ RingHom.ker χ → χ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) = χ jp ^ p) := by
  obtain ⟨h₀, h₁⟩ := 𝒞.jp_sub_j_pow_mem
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · have hp : Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))} ≤ RingHom.ker χ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
      exact CharP.cast_eq_zero S p
    haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
    obtain ⟨𝔯, h𝔯, h𝔯le⟩ := Ideal.exists_minimalPrimes_le hp
    rcases 𝒞.hminFin 𝔯 h𝔯 with rfl | rfl
    · exact Or.inl h𝔯le
    · exact Or.inr h𝔯le
  · have := h h₀
    rw [RingHom.mem_ker, map_sub, map_pow, sub_eq_zero] at this
    exact this
  · have := h h₁
    rw [RingHom.mem_ker, map_sub, map_pow, sub_eq_zero] at this
    exact this

theorem Cert.le_ker_and_not_le_ker_of_apply_eq_pow (𝒞 : Cert p κ jp W₀ W₁) {S : Type} [CommRing S] [IsDomain S] [CharP S p]
    (χ : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* S) :
    (χ jp = χ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ^ p → χ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ^ (p ^ 2) ≠ χ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →
      𝒞.𝔭₀ ≤ RingHom.ker χ ∧ ¬ 𝒞.𝔭₁ ≤ RingHom.ker χ) ∧
    (χ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) = χ jp ^ p → χ jp ^ (p ^ 2) ≠ χ jp →
      𝒞.𝔭₁ ≤ RingHom.ker χ ∧ ¬ 𝒞.𝔭₀ ≤ RingHom.ker χ) := by
  obtain ⟨hor, himp₀, himp₁⟩ := 𝒞.ker_dichotomy χ
  constructor
  · intro heq hne
    have hnot : ¬ 𝒞.𝔭₁ ≤ RingHom.ker χ := fun h1 => hne (by
      have e := himp₁ h1

      conv_rhs => rw [e, heq, ← pow_mul, ← sq])
    exact ⟨hor.resolve_right hnot, hnot⟩
  · intro heq hne
    have hnot : ¬ 𝒞.𝔭₀ ≤ RingHom.ker χ := fun h0 => hne (by
      have e := himp₀ h0
      conv_rhs => rw [e, heq, ← pow_mul, ← sq])
    exact ⟨hor.resolve_left hnot, hnot⟩

end BranchA
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

end TwoLinesAsm
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel"
open scoped TensorProduct

namespace RingStalk

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (O : Type u) [CommRing O] [Algebra R O]

noncomputable abbrev XO := pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))

private noncomputable abbrev _root_.RingStalk.PFin := pullback (ιFin R F j) (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))))

p2m_export "RingStalk" "PFin"

private noncomputable abbrev _root_.RingStalk.gFin : PFin R F j O ⟶ XO R F j O := pullback.snd _ _

p2m_export "RingStalk" "gFin"

private noncomputable def _root_.RingStalk.isoFin : PFin R F j O ≅ Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O)) :=
  pullbackRightPullbackFstIso (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))) (ιFin R F j) ≪≫
    pullback.congrHom (ιFin_toBase R F j) rfl ≪≫ pullbackSpecIso R ↥(chartAlgFin R F j) O

p2m_export "RingStalk" "isoFin"

noncomputable def chartFin : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O)) ⟶ XO R F j O :=
  (isoFin R F j O).inv ≫ gFin R F j O

scoped instance : IsOpenImmersion (chartFin R F j O) := by
  unfold chartFin; infer_instance

theorem chartFin_fst : chartFin R F j O ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j)) (B := O))) ≫
      ιFin R F j := by
  have hc : gFin R F j O ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))) =
      pullback.fst (ιFin R F j) _ ≫ ιFin R F j := pullback.condition.symm
  unfold chartFin isoFin
  simp only [Iso.trans_inv, Category.assoc, hc]
  rw [pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_inv]
  erw [pullback.lift_fst_assoc]
  rw [Category.comp_id, pullbackSpecIso_inv_fst_assoc]

theorem chartFin_snd : chartFin R F j O ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := O)).toRingHom) := by
  have hc : gFin R F j O ≫ pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))) =
      pullback.snd (ιFin R F j) _ ≫ pullback.snd _ _ := rfl
  unfold chartFin isoFin
  simp only [Iso.trans_inv, Category.assoc, hc]
  rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackSpecIso_inv_snd]
  rfl

theorem chartFin_comp_map {O' : Type u} [CommRing O'] [Algebra R O'] (φ : O →ₐ[R] O')
    (h₁ : toBase R F j ≫ 𝟙 _ = 𝟙 _ ≫ toBase R F j)
    (h₂ : Spec.map (CommRingCat.ofHom (algebraMap R O')) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R O))) :
    chartFin R F j O' ≫ pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) h₁ h₂ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R ↥(chartAlgFin R F j)) φ).toRingHom) ≫
        chartFin R F j O := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, chartFin_fst, Category.comp_id, Category.assoc, chartFin_fst,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    simp
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, chartFin_snd, Category.assoc, chartFin_snd, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2

theorem range_chartFin : Set.range (chartFin R F j O).base =
    (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))).base ⁻¹' Set.range (ιFin R F j).base := by
  rw [chartFin, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hsurj : Function.Surjective (isoFin R F j O).inv.base := (isoFin R F j O).inv.homeomorph.surjective
  rw [hsurj.range_eq, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

private noncomputable def _root_.RingStalk.stalkIso (𝔮 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] O)) :
    (XO R F j O).presheaf.stalk ((chartFin R F j O).base 𝔮) ≅ CommRingCat.of (Localization.AtPrime 𝔮.asIdeal) :=
  asIso ((chartFin R F j O).stalkMap 𝔮) ≪≫ Spec.stalkIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O)) 𝔮

p2m_export "RingStalk" "stalkIso"

theorem mem_image_top (𝔮 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] O)) :
    (chartFin R F j O).base 𝔮 ∈ (chartFin R F j O) ''ᵁ ⊤ := ⟨𝔮, trivial, rfl⟩

noncomputable def sectionOf (r : ↥(chartAlgFin R F j) ⊗[R] O) :
    Γ(XO R F j O, (chartFin R F j O) ''ᵁ ⊤) :=
  ((chartFin R F j O).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O))).inv r)

set_option maxHeartbeats 1600000 in

theorem stalkIso_germ_sectionOf (𝔮 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] O)) (r : ↥(chartAlgFin R F j) ⊗[R] O) :
    (stalkIso R F j O 𝔮).hom ((XO R F j O).presheaf.germ ((chartFin R F j O) ''ᵁ ⊤) ((chartFin R F j O).base 𝔮)
        (mem_image_top R F j O 𝔮) (sectionOf R F j O r)) =
      algebraMap _ (Localization.AtPrime 𝔮.asIdeal) r := by
  have h1 := Scheme.Hom.germ_stalkMap (chartFin R F j O) ((chartFin R F j O) ''ᵁ ⊤) 𝔮 (mem_image_top R F j O 𝔮)
  have h2 := Spec.germ_stalkMapIso_hom (R := CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O)) 𝔮
  have h2' : ∀ s, (Spec.stalkIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O)) 𝔮).hom
      ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O))).presheaf.germ ⊤ 𝔮 trivial s) =
      algebraMap _ (Localization.AtPrime 𝔮.asIdeal) ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] O))).hom s) := by
    intro s
    have := congrArg (fun φ => φ.hom s) h2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  simp only [stalkIso, sectionOf, Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply ((XO R F j O).presheaf.germ _ _ (mem_image_top R F j O 𝔮))
    ((chartFin R F j O).stalkMap 𝔮), h1, ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app_apply,
    TopCat.Presheaf.germ_res_apply]
  erw [h2']
  simp

end RingStalk
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel"
open scoped TensorProduct

noncomputable section

namespace OggT

variable (p : ℕ) [Fact p.Prime]

def uF : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, modularUnitSeries_mem_modularFunctionFieldFull p⟩

def uA : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := ⟨uF p, (ModularCurve.modularUnitSeries_mem_chartAlgFin_int p _).1⟩

def vA : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := ⟨(p : ↥(modularFunctionFieldFull p)) ^ 12 * (uF p)⁻¹, (ModularCurve.modularUnitSeries_mem_chartAlgFin_int p _).2⟩

@[scoped simp] theorem coe_uF : ((uF p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = modularUnitSeries p := rfl

theorem uF_ne_zero : uF p ≠ 0 := fun h =>
  modularUnitSeries_ne_zero p (by simpa using congrArg Subtype.val h)

theorem uA_mul_vA : uA p * vA p = ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ^ 12 := by
  apply Subtype.ext
  change (uF p) * ((p : ↥(modularFunctionFieldFull p)) ^ 12 * (uF p)⁻¹) = (((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ^ 12 : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ (uF_ne_zero p), mul_one]
  push_cast
  rfl

section BC

variable (O : Type) [CommRing O] (κ : Type) [CommRing κ] (toκ : O →+* κ)

def hmap : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] O →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) toκ.toIntAlgHom).toRingHom

@[scoped simp] theorem hmap_tmul (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (o : O) : hmap p O κ toκ (a ⊗ₜ o) = a ⊗ₜ toκ o := by
  simp [hmap, RingHom.toIntAlgHom]

theorem bc_fst : DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  unfold DRModel.baseChangeMap; rw [pullback.lift_fst, Category.comp_id]

theorem bc_snd : DRModel.baseChangeMap (p := p) toκ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
  unfold DRModel.baseChangeMap; rw [pullback.lift_snd]

theorem chartFin_bc : RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ ≫ DRModel.baseChangeMap (p := p) toκ =
    Spec.map (CommRingCat.ofHom (hmap p O κ toκ)) ≫ RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O := by
  unfold DRModel.baseChangeMap
  exact RingStalk.chartFin_comp_map ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O toκ.toIntAlgHom _ _

theorem bc_chartFin_base (𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)) :
    (DRModel.baseChangeMap (p := p) toκ).base ((RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base 𝔮) =
      (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).base (PrimeSpectrum.comap (hmap p O κ toκ) 𝔮) := by
  have := congrArg (fun f => f.base 𝔮) (chartFin_bc p O κ toκ)
  simp at this
  exact this

end BC
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk"

section Lines

variable [NeZero p] {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (ZMod p) κ]
  {jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))} {W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p)}

theorem chartFin_mem_range_es_Dinf_iff (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) (𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)) :
    (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base 𝔮 ∈ Set.range (GLUECI.es 𝒞.Dinf).base ↔
      𝒞.𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤ 𝔮.asIdeal := by
  have h := 𝒞.gFin_mem_range_es_Dinf_iff ((GLUECI.isoFin 𝒞.Dinf).inv.base 𝔮)
  have e1 : (GLUECI.isoFin 𝒞.Dinf).hom.base ((GLUECI.isoFin 𝒞.Dinf).inv.base 𝔮) = 𝔮 := by
    change ((GLUECI.isoFin 𝒞.Dinf).inv ≫ (GLUECI.isoFin 𝒞.Dinf).hom).base 𝔮 = 𝔮
    rw [Iso.inv_hom_id]; rfl
  rw [e1] at h
  exact h

theorem chartFin_mem_range_es_Dzero_iff (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) (𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ)) :
    (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base 𝔮 ∈ Set.range (GLUECI.es 𝒞.Dzero).base ↔
      𝒞.𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤ 𝔮.asIdeal := by
  have h := 𝒞.gFin_mem_range_es_Dzero_iff ((GLUECI.isoFin 𝒞.Dinf).inv.base 𝔮)
  have e1 : (GLUECI.isoFin 𝒞.Dinf).hom.base ((GLUECI.isoFin 𝒞.Dinf).inv.base 𝔮) = 𝔮 := by
    change ((GLUECI.isoFin 𝒞.Dinf).inv ≫ (GLUECI.isoFin 𝒞.Dinf).hom).base 𝔮 = 𝔮
    rw [Iso.inv_hom_id]; rfl
  rw [e1] at h
  exact h

end Lines
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk"

section GermUnits

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (O : Type u) [CommRing O] [Algebra R O]

theorem isUnit_iff_of_iso {A B : CommRingCat} (e : A ≅ B) (a : A) : IsUnit a ↔ IsUnit (e.hom a) := by
  constructor
  · exact fun h => h.map e.hom.hom
  · intro h
    have := h.map e.inv.hom
    simpa using this

theorem isUnit_germ_sectionOf_iff {w : ↥(RingStalk.XO R F j O)} (𝔔 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] O))
    (hw : w = (RingStalk.chartFin R F j O).base 𝔔) (hwU : w ∈ (RingStalk.chartFin R F j O) ''ᵁ ⊤) (r : ↥(chartAlgFin R F j) ⊗[R] O) :
    IsUnit ((RingStalk.XO R F j O).presheaf.germ _ w hwU (RingStalk.sectionOf R F j O r)) ↔ r ∉ 𝔔.asIdeal := by
  subst hw
  rw [isUnit_iff_of_iso (RingStalk.stalkIso R F j O 𝔔), RingStalk.stalkIso_germ_sectionOf]
  exact IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔.asIdeal r

theorem germ_sectionOf_mem_maximalIdeal_iff {w : ↥(RingStalk.XO R F j O)} (𝔔 : PrimeSpectrum (↥(chartAlgFin R F j) ⊗[R] O))
    (hw : w = (RingStalk.chartFin R F j O).base 𝔔) (hwU : w ∈ (RingStalk.chartFin R F j O) ''ᵁ ⊤) (r : ↥(chartAlgFin R F j) ⊗[R] O) :
    (RingStalk.XO R F j O).presheaf.germ _ w hwU (RingStalk.sectionOf R F j O r) ∈ IsLocalRing.maximalIdeal _ ↔ r ∈ 𝔔.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_germ_sectionOf_iff R F j O 𝔔 hw hwU r, not_not]

end GermUnits
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk"

section GenericPoints

variable [NeZero p] {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (ZMod p) κ]
  {jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))} {W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p)}

def linePrime₀ (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) :=
  ⟨𝒞.𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ), by
    rw [← 𝒞.hKF₀]; exact RingHom.ker_isPrime _⟩

def linePrime₁ (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) :=
  ⟨𝒞.𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ), by
    rw [← 𝒞.hKF₁]; exact RingHom.ker_isPrime _⟩

theorem closure_chartFin_eq_of_forall_mem_iff {S : Set ↥(RingStalk.XO ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)}
    (hS : IsIrreducible S) (hSc : IsClosed S) (𝔓 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ))
    (hread : ∀ 𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ), (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base 𝔮 ∈ S ↔ 𝔓.asIdeal ≤ 𝔮.asIdeal) :
    closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base 𝔓} = S := by
  have hζ : (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base 𝔓 ∈ S := (hread 𝔓).mpr le_rfl

  obtain ⟨g, hg⟩ := QuasiSober.sober hS hSc

  have hgU : g ∈ Set.range (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base := by
    have hopen : IsOpen (Set.range (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base) := (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).isOpenEmbedding.isOpen_range
    exact (hg.mem_open_set_iff hopen).mpr ⟨_, hζ, 𝔓, rfl⟩
  obtain ⟨𝔮g, rfl⟩ := hgU

  set 𝔮 : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) := 𝔮g with h𝔮
  have h1 : 𝔓.asIdeal ≤ 𝔮.asIdeal := (hread 𝔮).mp hg.mem
  have h2 : 𝔮 ⤳ 𝔓 := ((RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).isOpenEmbedding.isInducing.specializes_iff).mp (hg.specializes hζ)
  have h3 : 𝔮 = 𝔓 := le_antisymm ((PrimeSpectrum.le_iff_specializes 𝔮 𝔓).mpr h2) h1
  rw [← h3]
  exact hg

theorem closure_line₀_eq (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) :
    closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (linePrime₀ p 𝒞)} = Set.range (GLUECI.es 𝒞.Dinf).base := by
  haveI := GLUECI.isClosedImmersion_es 𝒞.Dinf
  obtain ⟨M, e, -⟩ := AlgebraicCurve.CurveModel.exists_curveModel_ratFunc κ
  have hr : Set.range (e.hom ≫ GLUECI.es 𝒞.Dinf).base = Set.range (GLUECI.es 𝒞.Dinf).base := TwoLinesAsm.range_iso_hom_comp e _
  exact closure_chartFin_eq_of_forall_mem_iff p (hr ▸ TwoLinesAsm.FbPlus.isIrreducible_range_of_irreducibleSpace (e.hom ≫ GLUECI.es 𝒞.Dinf))
    (TwoLinesAsm.FbPlus.isClosed_range_of_isClosedImmersion _) (linePrime₀ p 𝒞) (chartFin_mem_range_es_Dinf_iff p 𝒞)

theorem closure_line₁_eq (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) :
    closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (linePrime₁ p 𝒞)} = Set.range (GLUECI.es 𝒞.Dzero).base := by
  haveI := GLUECI.isClosedImmersion_es 𝒞.Dzero
  obtain ⟨M, e, -⟩ := AlgebraicCurve.CurveModel.exists_curveModel_ratFunc κ
  have hr : Set.range (e.hom ≫ GLUECI.es 𝒞.Dzero).base = Set.range (GLUECI.es 𝒞.Dzero).base := TwoLinesAsm.range_iso_hom_comp e _
  exact closure_chartFin_eq_of_forall_mem_iff p (hr ▸ TwoLinesAsm.FbPlus.isIrreducible_range_of_irreducibleSpace (e.hom ≫ GLUECI.es 𝒞.Dzero))
    (TwoLinesAsm.FbPlus.isClosed_range_of_isClosedImmersion _) (linePrime₁ p 𝒞) (chartFin_mem_range_es_Dzero_iff p 𝒞)

end GenericPoints
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk"

section Xi

theorem image_closure_singleton_eq {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (a : X)
    (hc : IsClosed (f '' closure {a})) : f '' closure {a} = closure {f a} := by
  apply le_antisymm
  · have := image_closure_subset_closure_image hf (s := {a})
    rwa [Set.image_singleton] at this
  · apply closure_minimal _ hc
    rintro _ rfl
    exact ⟨a, subset_closure rfl, rfl⟩

variable [NeZero p] {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (ZMod p) κ]
  {jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))} {W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p)}
  (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (toκ : O →+* κ)

include hϖ in

theorem exists_ξ_eq_chartFin (𝒞 : TwoLinesAsm.Cert p κ jp W₀ W₁) :
    ∃ swap : Bool,
      𝔛.ξinf O κ toκ = (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).base (PrimeSpectrum.comap (hmap p O κ toκ) (if swap then linePrime₁ p 𝒞 else linePrime₀ p 𝒞)) ∧
      𝔛.ξzero O κ toκ = (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).base (PrimeSpectrum.comap (hmap p O κ toκ) (if swap then linePrime₀ p 𝒞 else linePrime₁ p 𝒞)) := by
  obtain ⟨swap, hI, hZ⟩ := 𝒞.exists_swap_range_comp_eq 𝔛
  obtain ⟨hIr, hIc⟩ := 𝔛.range_compInf_comp_baseChangeMap_eq_closure_and_isClosed p O hϖ κ toκ
  obtain ⟨hZr, hZc⟩ := 𝔛.range_compZero_comp_baseChangeMap_eq_closure_and_isClosed p O hϖ κ toκ
  refine ⟨swap, ?_, ?_⟩
  ·
    have hζ : Set.range (𝔛.compInf κ).base = closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (if swap then linePrime₁ p 𝒞 else linePrime₀ p 𝒞)} := by
      rw [hI]; cases swap
      · exact (closure_line₀_eq p 𝒞).symm
      · exact (closure_line₁_eq p 𝒞).symm
    have h1 : Set.range (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base =
        (DRModel.baseChangeMap toκ).base '' closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (if swap then linePrime₁ p 𝒞 else linePrime₀ p 𝒞)} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hζ]
    have h2 := image_closure_singleton_eq (DRModel.baseChangeMap toκ).base.hom.continuous
      ((RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (if swap then linePrime₁ p 𝒞 else linePrime₀ p 𝒞)) (by rw [← h1]; exact hIc)
    rw [h1, h2, bc_chartFin_base] at hIr
    exact ((inseparable_iff_closure_eq.mpr hIr).eq).symm
  · have hζ : Set.range (𝔛.compZero κ).base = closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (if swap then linePrime₀ p 𝒞 else linePrime₁ p 𝒞)} := by
      rw [hZ]; cases swap
      · exact (closure_line₁_eq p 𝒞).symm
      · exact (closure_line₀_eq p 𝒞).symm
    have h1 : Set.range (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base =
        (DRModel.baseChangeMap toκ).base '' closure {(RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (if swap then linePrime₀ p 𝒞 else linePrime₁ p 𝒞)} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hζ]
    have h2 := image_closure_singleton_eq (DRModel.baseChangeMap toκ).base.hom.continuous
      ((RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base (if swap then linePrime₀ p 𝒞 else linePrime₁ p 𝒞)) (by rw [← h1]; exact hZc)
    rw [h1, h2, bc_chartFin_base] at hZr
    exact ((inseparable_iff_closure_eq.mpr hZr).eq).symm

end Xi
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk"

theorem crossingPt_mem_preimage_chartFin_STUB (hp : 5 ≤ p) (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (𝔛.crossingPt O κ toκ n) ∈
      (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤ :=
  ModularCurve.DRModelPackage.crossingPt_mem_preimage_chartFin p hp 𝔛 O κ toκ n

set_option maxHeartbeats 3200000 in

theorem exists_mul_eq_baseGerm_pow_twelve
    (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    ∃ t t' : (DRModelPackage.baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n),
      t * t' = DRModelPackage.baseGerm O (𝔛.crossingPt O κ toκ n) (p : O) ^ 12 ∧
      t ∈ IsLocalRing.maximalIdeal _ ∧
      (IsUnit (((DRModelPackage.baseChangeO p O).presheaf.stalkSpecializes hinf).hom t) ∨
        IsUnit (((DRModelPackage.baseChangeO p O).presheaf.stalkSpecializes hzero).hom t)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hne, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  obtain ⟨𝒞⟩ := TwoLinesAsm.nonempty_cert p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ κ

  obtain ⟨Pu, Pz, -, -, hPuz, hmin, -, huPu, huPz, -⟩ := HpoolLevelRing.exists_pFibre_dictionary p hp
    (modularUnitSeries_mem_modularFunctionFieldFull p) (uA p) (Or.inl rfl)
  have hPu' : Pu ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes := by rw [hmin]; exact Set.mem_insert _ _
  have hPz' : Pz ∈ (Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))}).minimalPrimes := by rw [hmin]; exact Set.mem_insert_of_mem _ rfl

  set y : ↥(RingStalk.XO ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) := (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base n with hy
  have hxy : 𝔛.crossingPt O κ toκ n = (DRModel.baseChangeMap toκ).base y := rfl
  have hyI : y ∈ Set.range (𝔛.compInf κ).base := ⟨(pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n, rfl⟩
  have hyZ : y ∈ Set.range (𝔛.compZero κ).base := ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, by
    rw [hy, pullback.condition]; rfl⟩
  obtain ⟨swap0, hI, hZ⟩ := 𝒞.exists_swap_range_comp_eq 𝔛
  have hyD : y ∈ Set.range (GLUECI.es 𝒞.Dinf).base ∧ y ∈ Set.range (GLUECI.es 𝒞.Dzero).base := by
    cases swap0
    · exact ⟨hI ▸ hyI, hZ ▸ hyZ⟩
    · exact ⟨hZ ▸ hyZ, hI ▸ hyI⟩

  have hyfin : y ∈ Set.range (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base := by
    rw [RingStalk.range_chartFin, Set.mem_preimage, ← bc_fst p O κ toκ, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      ← hxy]
    obtain ⟨z, -, hz⟩ := crossingPt_mem_preimage_chartFin_STUB p hp 𝔛 O κ toκ n
    exact ⟨z, hz⟩
  obtain ⟨𝔮y, hq⟩ := hyfin
  have h0 : 𝒞.𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤ 𝔮y.asIdeal :=
    (chartFin_mem_range_es_Dinf_iff p 𝒞 𝔮y).mp (hq ▸ hyD.1)
  have h1 : 𝒞.𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ≤ 𝔮y.asIdeal :=
    (chartFin_mem_range_es_Dzero_iff p 𝒞 𝔮y).mp (hq ▸ hyD.2)
  set 𝔮x : PrimeSpectrum (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] O) := PrimeSpectrum.comap (hmap p O κ toκ) 𝔮y with h𝔮x
  have hx : 𝔛.crossingPt O κ toκ n = (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).base 𝔮x := by rw [hxy, ← hq, bc_chartFin_base]

  have hu𝔮 : (uA p) ⊗ₜ[ℤ] (1 : O) ∈ 𝔮x.asIdeal := by
    show hmap p O κ toκ ((uA p) ⊗ₜ[ℤ] (1 : O)) ∈ 𝔮y.asIdeal
    rw [hmap_tmul, map_one]
    rcases 𝒞.hminFin Pz hPz' with h | h
    · exact h0 (Ideal.mem_map_of_mem _ (h ▸ huPz))
    · exact h1 (Ideal.mem_map_of_mem _ (h ▸ huPz))

  obtain ⟨swap, hξI, hξZ⟩ := exists_ξ_eq_chartFin p 𝔛 O hϖ toκ 𝒞

  have hunit : ∀ b : Bool, Pu = (if b then 𝒞.𝔭₁ else 𝒞.𝔭₀) →
      (uA p) ⊗ₜ[ℤ] (1 : O) ∉ (PrimeSpectrum.comap (hmap p O κ toκ) (if b then linePrime₁ p 𝒞 else linePrime₀ p 𝒞)).asIdeal := by
    intro b hb hmem
    apply huPu
    change hmap p O κ toκ ((uA p) ⊗ₜ[ℤ] (1 : O)) ∈ (if b then linePrime₁ p 𝒞 else linePrime₀ p 𝒞).asIdeal at hmem
    rw [hmap_tmul, map_one] at hmem
    rw [hb]
    cases b
    · exact (𝒞.hA₀ (uA p)).mp (𝒞.hKF₀ ▸ hmem)
    · exact (𝒞.hA₁ (uA p)).mp (𝒞.hKF₁ ▸ hmem)

  revert hinf hzero
  rw [hx]
  intro hinf hzero
  have hxU := RingStalk.mem_image_top ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O 𝔮x
  refine ⟨(RingStalk.XO ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ _ _ hxU (RingStalk.sectionOf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ((uA p) ⊗ₜ[ℤ] (1 : O))),
    (RingStalk.XO ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ _ _ hxU (RingStalk.sectionOf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ((vA p) ⊗ₜ[ℤ] (1 : O))),
    ?_, ?_, ?_⟩
  ·
    set G := (RingStalk.XO ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ _ _ hxU with hG
    show G.hom _ * G.hom _ = _
    rw [← map_mul G.hom]
    have hsec : RingStalk.sectionOf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ((uA p) ⊗ₜ[ℤ] (1 : O)) *
        RingStalk.sectionOf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ((vA p) ⊗ₜ[ℤ] (1 : O)) =
        ((p : ℕ) : Γ(RingStalk.XO ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O, (RingStalk.chartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ''ᵁ ⊤)) ^ 12 := by
      simp only [RingStalk.sectionOf, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, uA_mul_vA]
      have hincl : ((((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ^ 12) ⊗ₜ[ℤ] (1 : O) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] O) =
          (Algebra.TensorProduct.includeLeftRingHom : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] O) (((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ^ 12) := rfl
      simp only [hincl, map_pow, map_natCast]
    rw [hsec, map_pow, map_natCast]

    simp only [DRModelPackage.baseGerm, map_natCast]
  ·
    exact (germ_sectionOf_mem_maximalIdeal_iff ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O 𝔮x rfl hxU _).mpr hu𝔮
  ·
    have hb : ∃ b : Bool, Pu = (if b then 𝒞.𝔭₁ else 𝒞.𝔭₀) := by
      rcases 𝒞.hminFin Pu hPu' with h | h
      · exact ⟨false, by simpa using h⟩
      · exact ⟨true, by simpa using h⟩
    obtain ⟨b, hb⟩ := hb
    have key := hunit b hb
    cases swap <;> cases b
    · left
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact (isUnit_germ_sectionOf_iff ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O _ hξI _ _).mpr key
    · right
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact (isUnit_germ_sectionOf_iff ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O _ hξZ _ _).mpr key
    · right
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact (isUnit_germ_sectionOf_iff ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O _ hξZ _ _).mpr key
    · left
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact (isUnit_germ_sectionOf_iff ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O _ hξI _ _).mpr key

end OggT
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggT"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.GLUECI P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.TensorAdapt P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.BranchData P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.RingStalk P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.OggT"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing.AlgebraicGeometry ModularCurve ModularCurve.DRModelPackage"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    ∃ t t' : (baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n),
      t * t' = baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O) ^ 12 ∧
      t ∈ IsLocalRing.maximalIdeal ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)) ∧
      (IsUnit (((baseChangeO p O).presheaf.stalkSpecializes hinf).hom t) ∨
        IsUnit (((baseChangeO p O).presheaf.stalkSpecializes hzero).hom t)) :=
  OggT.exists_mul_eq_baseGerm_pow_twelve p hp 𝔛 O hϖ κ toκ n hinf hzero

end S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing (solution)
