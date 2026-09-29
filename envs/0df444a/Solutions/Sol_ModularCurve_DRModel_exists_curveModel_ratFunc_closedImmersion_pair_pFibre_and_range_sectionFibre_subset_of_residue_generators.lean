-- Prove2me | solution 1 for ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7dd72f53-ba88-5d82-a513-0fc483a9591a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgInf_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_chartAlg_int
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_ratFunc
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
import Theorems.Thm_ModularCurve_DRModel_map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_int_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_ModularCurve_IsFrickeAutFull_eq_frickeInvolutionFull
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel"

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
    first
      | simpa only [RingHom.algebraMap_toAlgebra, map_pow] using h
      | (have h' := h; simp only [RingHom.algebraMap_toAlgebra, map_pow] at h' ⊢; exact h')
      | (have h' := h; simp only [RingHom.algebraMap_toAlgebra, map_pow] at h'; exact h')
      | exact h
      | (simpa only [RingHom.algebraMap_toAlgebra, map_pow, Function.comp_def] using h)
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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI"

set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel"

open scoped TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.range_pullbackFst pullbackSpecIso_inv_snd Surjective Scheme.Hom affine_isReduced_iff Scheme.Pullback.range_map Scheme.IsLocallyDirected.ι_eq_ι_iff isIso_iff_isOpenImmersion_and_epi_base IsZariskiLocalAtTarget Spec IsIntegral Spec.map Scheme pullbackSpecIso IsOpenImmersion.range_pullbackSnd IsOpenImmersion Scheme.Pullback.openCoverOfBase IsReduced.of_openCover pullbackSpecIso_inv_fst IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced IsOpenImmersion.isoOfRangeEq Spec.map_id Scheme.Cover.mkOfCovers IsZariskiLocalAtTarget.of_openCover pullbackSpecIso_hom_fst isReduced_of_isOpenImmersion Scheme.forgetToTop Scheme.Hom.comp_apply Scheme.Cover IsOpenImmersion.isoOfRangeEq_hom_fac"
p2m_open "AlgebraicGeometry"

namespace Spec p2m_export "AlgebraicGeometry.Spec" "map_comp map map_injective preimage map_id" end Spec
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

p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec"
p2m_open_scoped "AlgebraicGeometry.Spec" in
@[scoped simp]
theorem Spec.isoOfRingEquiv_inv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (Spec.isoOfRingEquiv e).inv = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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

private theorem _root_.GLUECI.isReduced_pullback_es
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

p2m_export "GLUECI" "isReduced_pullback_es"

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

private theorem _root_.GLUECI.natCard_pullback_es
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

p2m_export "GLUECI" "natCard_pullback_es"
end Pair
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

end GLUECI
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel"

open scoped TensorProduct

noncomputable section

namespace GLUECI

open AlgebraicCurve.TwoChartIntegralModel

section Generic

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
  {κ : Type u} [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

omit [Fact (t ≠ 0)] in

theorem IInf_sup_IInf_sup_span_eq_top (D₀ D₁ : GlueDatum R F j κ t)
    {a₀ a₁ c : ↥(chartAlgInf R F j)}
    (ha₀ : a₀ ⊗ₜ[R] (1 : κ) ∈ D₀.IInf) (ha₁ : a₁ ⊗ₜ[R] (1 : κ) ∈ D₁.IInf)
    (hsum : a₀ + a₁ + c * jInvChartInf R F j = 1) :
    D₀.IInf ⊔ D₁.IInf ⊔ Ideal.span {jInvChartInf R F j ⊗ₜ[R] (1 : κ)} = ⊤ := by
  rw [Ideal.eq_top_iff_one,
    show (1 : ↥(chartAlgInf R F j) ⊗[R] κ) = (1 : ↥(chartAlgInf R F j)) ⊗ₜ[R] (1 : κ) from rfl,
    ← hsum, TensorProduct.add_tmul, TensorProduct.add_tmul]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mem_sup_left (Ideal.mem_sup_left ha₀)
  · exact Ideal.mem_sup_left (Ideal.mem_sup_right ha₁)
  · apply Ideal.mem_sup_right
    have hmul : (c * jInvChartInf R F j) ⊗ₜ[R] (1 : κ) =
        (c ⊗ₜ[R] (1 : κ)) * (jInvChartInf R F j ⊗ₜ[R] (1 : κ)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

omit [Fact (t ≠ 0)] in

theorem tmul_one_mem_IInf_of_eq_map (D : GlueDatum R F j κ t) {𝔮 : Ideal ↥(chartAlgInf R F j)}
    (hKI : D.IInf = 𝔮.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ))
    {a : ↥(chartAlgInf R F j)} (ha : a ∈ 𝔮) : a ⊗ₜ[R] (1 : κ) ∈ D.IInf := by
  rw [hKI]
  exact Ideal.mem_map_of_mem _ ha

theorem isReduced_pullback_es_of_map (D₀ D₁ : GlueDatum R F j κ t)
    {𝔭₀ 𝔭₁ : Ideal ↥(chartAlgFin R F j)} {𝔮₀ 𝔮₁ : Ideal ↥(chartAlgInf R F j)}
    (hKF₀ : D₀.IFin = 𝔭₀.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ))
    (hKF₁ : D₁.IFin = 𝔭₁.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ))
    (hKI₀ : D₀.IInf = 𝔮₀.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ))
    (hKI₁ : D₁.IInf = 𝔮₁.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ))
    {a₀ a₁ c : ↥(chartAlgInf R F j)} (ha₀ : a₀ ∈ 𝔮₀) (ha₁ : a₁ ∈ 𝔮₁)
    (hsum : a₀ + a₁ + c * jInvChartInf R F j = 1)
    (hred : _root_.IsReduced ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸
      (𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ) ⊔
        𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ)))) :
    IsReduced (pullback (es D₀) (es D₁)) := by
  refine isReduced_pullback_es_of_sup_eq_top D₀ D₁
    (IInf_sup_IInf_sup_span_eq_top D₀ D₁ (tmul_one_mem_IInf_of_eq_map D₀ hKI₀ ha₀)
      (tmul_one_mem_IInf_of_eq_map D₁ hKI₁ ha₁) hsum) ?_
  rw [hKF₀, hKF₁]
  exact hred

theorem natCard_pullback_es_of_map (D₀ D₁ : GlueDatum R F j κ t)
    {𝔭₀ 𝔭₁ : Ideal ↥(chartAlgFin R F j)} {𝔮₀ 𝔮₁ : Ideal ↥(chartAlgInf R F j)}
    (hKF₀ : D₀.IFin = 𝔭₀.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ))
    (hKF₁ : D₁.IFin = 𝔭₁.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ))
    (hKI₀ : D₀.IInf = 𝔮₀.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ))
    (hKI₁ : D₁.IInf = 𝔮₁.map
      (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j) ⊗[R] κ))
    {a₀ a₁ c : ↥(chartAlgInf R F j)} (ha₀ : a₀ ∈ 𝔮₀) (ha₁ : a₁ ∈ 𝔮₁)
    (hsum : a₀ + a₁ + c * jInvChartInf R F j = 1)
    {n : ℕ}
    (hcard : Nat.card (PrimeSpectrum ((↥(chartAlgFin R F j) ⊗[R] κ) ⧸
      (𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ) ⊔
        𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j) ⊗[R] κ)))) =
      n) :
    Nat.card ↥(pullback (es D₀) (es D₁)) = n := by
  rw [natCard_pullback_es_of_sup_eq_top D₀ D₁
    (IInf_sup_IInf_sup_span_eq_top D₀ D₁ (tmul_one_mem_IInf_of_eq_map D₀ hKI₀ ha₀)
      (tmul_one_mem_IInf_of_eq_map D₁ hKI₁ ha₁) hsum), hKF₀, hKF₁]
  exact hcard

end Generic
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

section Modular

open ModularCurve

variable (p : ℕ) [Fact p.Prime] [NeZero p]

omit [NeZero p] in

theorem sectionFibre_fst (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p))
    {κ : Type} [CommRing κ] (a : ℤ →+* κ) :
    DRModel.sectionFibre ε a ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom a) ≫ ε.1 := by
  delta DRModel.sectionFibre
  exact pullback.lift_fst _ _ _

omit [NeZero p] in

theorem sectionFibre_snd (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p))
    {κ : Type} [CommRing κ] (a : ℤ →+* κ) :
    DRModel.sectionFibre ε a ≫ pullback.snd _ _ = 𝟙 _ := by
  delta DRModel.sectionFibre
  exact pullback.lift_snd _ _ _

variable {κ : Type} [Field κ] {L : Type} [Field L] [Algebra κ L] {t : L} [Fact (t ≠ 0)]

theorem range_sectionFibre_subset_range_es_iff
    (D : GlueDatum ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ t)
    (ψ : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p))
    (hε : ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :
    Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range (es D).base ↔
      D.IInf ≤ RingHom.ker (secChar κ ψ).toRingHom :=
  range_subset_range_es_iff ψ (DRModel.sectionFibre ε (algebraMap ℤ κ))
    (by rw [sectionFibre_fst, hε]) (sectionFibre_snd p ε _) D

theorem disjoint_range_sectionFibre_range_es
    (D : GlueDatum ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ t)
    (ψ : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p))
    (hε : ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
    (h : ¬ D.IInf ≤ RingHom.ker (secChar κ ψ).toRingHom) :
    Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range (es D).base) :=
  disjoint_range_es_of_not_le ψ (DRModel.sectionFibre ε (algebraMap ℤ κ))
    (by rw [sectionFibre_fst, hε]) (sectionFibre_snd p ε _) D h

end Modular
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

end GLUECI
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry"

end TensorAdapt
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace C1Glue

theorem sup_sup_span_eq_top {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (J₀ J₁ : Ideal A) (I₀ I₁ : Ideal B) (h₀ : J₀.map f ≤ I₀) (h₁ : J₁.map f ≤ I₁)
    (s a₀ a₁ c : A) (ha₀ : a₀ ∈ J₀) (ha₁ : a₁ ∈ J₁) (hrel : a₀ + a₁ + c * s = 1) :
    I₀ ⊔ I₁ ⊔ Ideal.span {f s} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have : f a₀ + f a₁ + f c * f s = 1 := by rw [← map_mul, ← map_add, ← map_add, hrel, map_one]
  rw [← this]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mem_sup_left (Ideal.mem_sup_left (h₀ (Ideal.mem_map_of_mem f ha₀)))
  · exact Ideal.mem_sup_left (Ideal.mem_sup_right (h₁ (Ideal.mem_map_of_mem f ha₁)))
  · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

section Sec

variable {A : Type} [CommRing A] (κ : Type) [Field κ] (p : ℕ) [CharP κ p]

def secCharZ (ψ : A →+* ℤ) : A ⊗[ℤ] κ →ₐ[ℤ] κ :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℤ κ).comp { ψ with commutes' := fun n => by simp })
    (AlgHom.id ℤ κ) (fun _ _ => Commute.all _ _)

theorem secCharZ_tmul (ψ : A →+* ℤ) (a : A) (c : κ) : secCharZ κ ψ (a ⊗ₜ[ℤ] c) = (ψ a : κ) * c := by
  rw [secCharZ, Algebra.TensorProduct.lift_tmul]
  simp

variable {χT : Type} [FunLike χT (A ⊗[ℤ] κ) κ] [RingHomClass χT (A ⊗[ℤ] κ) κ]

theorem map_le_ker_of_char (ψ : A → ℤ) (χ : χT) (hχ : ∀ (a : A) (c : κ), χ (a ⊗ₜ[ℤ] c) = (ψ a : κ) * c)
    (J : Ideal A) (hJ : ∀ a ∈ J, (p : ℤ) ∣ ψ a) :
    J.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ≤ RingHom.ker χ := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, hχ, mul_one]
  obtain ⟨k, hk⟩ := hJ a ha
  rw [hk, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero κ p, zero_mul]

theorem not_map_le_ker_of_char [Fact p.Prime] (ψ : A → ℤ) (χ : χT) (hχ : ∀ (a : A) (c : κ), χ (a ⊗ₜ[ℤ] c) = (ψ a : κ) * c)
    (J : Ideal A) (hJ : ∃ a ∈ J, ¬ (p : ℤ) ∣ ψ a) :
    ¬ J.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ≤ RingHom.ker χ := by
  obtain ⟨a, ha, hndvd⟩ := hJ
  intro hle
  have h0 : χ (a ⊗ₜ[ℤ] (1 : κ)) = 0 := by
    have := hle (Ideal.mem_map_of_mem (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ha)
    rwa [RingHom.mem_ker] at this
  rw [hχ, mul_one] at h0
  apply hndvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) κ) := (ZMod.castHom (dvd_refl p) κ).injective
  apply hinj
  rw [map_intCast, map_zero]
  exact h0

end Sec
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

end C1Glue
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

p2m_open "ModularCurve AlgebraicCurve Polynomial AlgebraicGeometry.Polynomial"
open scoped TensorProduct

noncomputable section

namespace CrossingFin

section Unit

variable (p : ℕ) [hp : Fact p.Prime] [NeZero p]

def uF : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, modularUnitSeries_mem_modularFunctionFieldFull p⟩

omit hp in
@[scoped simp] theorem coe_uF : ((uF p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = modularUnitSeries p := rfl

omit hp in
theorem uF_ne_zero : uF p ≠ 0 := fun h =>
  modularUnitSeries_ne_zero p (by simpa using congrArg Subtype.val h)

def uA : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := ⟨uF p, (ModularCurve.modularUnitSeries_mem_chartAlgFin_int p _).1⟩

def vA : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := ⟨(p : ↥(modularFunctionFieldFull p)) ^ 12 * (uF p)⁻¹, (ModularCurve.modularUnitSeries_mem_chartAlgFin_int p _).2⟩

@[scoped simp] theorem coe_uA : ((uA p : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) = uF p := rfl

theorem uA_mul_vA : uA p * vA p = ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ^ 12 := by
  apply Subtype.ext
  change (uF p) * ((p : ↥(modularFunctionFieldFull p)) ^ 12 * (uF p)⁻¹) = (((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ^ 12 : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ (uF_ne_zero p), mul_one]
  simp

theorem uF_mem_and_inv_mem_of_gauss (hp5 : 5 ≤ p) (W₀ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull p), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) :
    uF p ∈ W₀ ∧ (uF p)⁻¹ ∈ W₀ := by
  classical
  obtain ⟨x, hx, hxκ⟩ :=
    ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet p hp5

  have hx0 : coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 := by
    intro h0
    let κ := AlgebraicClosure (ZMod p)
    have hS := hxκ κ (ssJSet_finite p κ).toFinset (fun a => Set.Finite.mem_toFinset _)
    have h1 : coeffMap (Int.castRingHom κ) x = 0 := by
      have : coeffMap (Int.castRingHom κ) x =
          coeffMap (algebraMap (ZMod p) κ) (coeffMap (Int.castRingHom (ZMod p)) x) := by
        rw [coeffMap_coeffMap]; exact coeffMap_congr (RingHom.ext_int _ _) x
      rw [this, h0, map_zero]
    rw [h1] at hS
    have hCa : ∀ a : κ, HahnSeries.C a = algebraMap κ (LaurentSeries κ) a := fun a => by
      rw [HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]
    refine absurd hS.symm (Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ ?_)
    intro h
    have heq : jqModC κ = algebraMap κ (LaurentSeries κ) a := by
      rw [← hCa]; exact sub_eq_zero.mp h
    exact ModularCurve.transcendental_jqModC κ (heq ▸ isAlgebraic_algebraMap a)
  have hcoeinv : (((uF p)⁻¹ : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = (modularUnitSeries p)⁻¹ :=
    map_inv₀ (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) (uF p)
  refine ⟨(hW₀ _).mpr ⟨x, 1, by rw [map_one]; exact one_ne_zero, ?_⟩,
    (hW₀ _).mpr ⟨1, x, hx0, ?_⟩⟩
  · rw [map_one, mul_one, hx]; rfl
  · rw [hcoeinv, hx, map_one, inv_mul_cancel₀ (modularUnitSeries_ne_zero p)]

theorem uF_mem_nonunits_of_swap (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits) (hu : uF p ∈ W₀ ∧ (uF p)⁻¹ ∈ W₀)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (σ : ↥(modularFunctionFieldFull p) ≃ₐ[ℚ] ↥(modularFunctionFieldFull p)) (hσj : σ (IgusaScheme.jFull p) = (jp : ↥(modularFunctionFieldFull p)))
    (hσjp : σ (jp : ↥(modularFunctionFieldFull p)) = IgusaScheme.jFull p)
    (hW₁ : ∀ f : ↥(modularFunctionFieldFull p), f ∈ W₁ ↔ σ f ∈ W₀) :
    uF p ∈ W₁.nonunits := by

  have key₁ : ∀ (m₁ : qExpand ℚ 1 jq ∈ modularFunctionFieldFull p)
      (m₂ : qExpand ℚ p jq ∈ modularFunctionFieldFull p),
      σ ⟨qExpand ℚ 1 jq, m₁⟩ = ⟨qExpand ℚ p jq, m₂⟩ := fun m₁ m₂ => by
    have e1 : (⟨qExpand ℚ 1 jq, m₁⟩ : ↥(modularFunctionFieldFull p)) = IgusaScheme.jFull p := Subtype.ext (qExpand_one_apply jq)
    have e2 : (⟨qExpand ℚ p jq, m₂⟩ : ↥(modularFunctionFieldFull p)) = (jp : ↥(modularFunctionFieldFull p)) := Subtype.ext hjp.symm
    rw [e1, e2, hσj]
  have key₂ : ∀ (m₁ : qExpand ℚ p jq ∈ modularFunctionFieldFull p)
      (m₂ : qExpand ℚ 1 jq ∈ modularFunctionFieldFull p),
      σ ⟨qExpand ℚ p jq, m₁⟩ = ⟨qExpand ℚ 1 jq, m₂⟩ := fun m₁ m₂ => by
    have e1 : (⟨qExpand ℚ 1 jq, m₂⟩ : ↥(modularFunctionFieldFull p)) = IgusaScheme.jFull p := Subtype.ext (qExpand_one_apply jq)
    have e2 : (⟨qExpand ℚ p jq, m₁⟩ : ↥(modularFunctionFieldFull p)) = (jp : ↥(modularFunctionFieldFull p)) := Subtype.ext hjp.symm
    rw [e1, e2, hσjp]
  have hfr : IsFrickeAutFull p σ := by
    intro a b hab _ _
    rcases (Nat.dvd_prime hp.out).mp (Dvd.intro b hab) with rfl | rfl
    · obtain rfl : b = p := by simpa using hab
      exact key₁ _ _
    · obtain rfl : b = 1 := (mul_right_eq_self₀.mp hab).resolve_right hp.out.ne_zero
      exact key₂ _ _
  have hσ : σ = frickeInvolutionFull p := ModularCurve.IsFrickeAutFull.eq_frickeInvolutionFull hfr

  have hσu : σ (uF p) = ((p : ℕ) : ↥(modularFunctionFieldFull p)) ^ 12 * (uF p)⁻¹ := by
    apply Subtype.ext
    change ((σ (uF p) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ) (((p : ℕ) : ↥(modularFunctionFieldFull p)) ^ 12 * (uF p)⁻¹)
    rw [map_mul, map_pow, map_natCast, map_inv₀, hσ]
    change ((frickeInvolutionFull p ⟨modularUnitSeries p, modularUnitSeries_mem_modularFunctionFieldFull p⟩
      : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = _
    rw [ModularCurve.coe_frickeInvolutionFull_modularUnitSeries p
      (modularUnitSeries_mem_modularFunctionFieldFull p), ← HahnSeries.C_mul_eq_smul, map_pow,
      map_natCast]
    rfl

  have hu0 : uF p ≠ 0 := uF_ne_zero p
  have hpF : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [ValuationSubring.mem_nonunits_iff] at hp₀ ⊢
  have h1 : W₁.valuation (uF p) < 1 ↔ 1 < W₁.valuation (uF p)⁻¹ := by
    rw [Valuation.one_lt_val_iff _ (inv_ne_zero hu0), inv_inv]
  rw [h1, lt_iff_not_ge, ValuationSubring.valuation_le_one_iff, hW₁, map_inv₀, hσu]
  intro hmem
  have hinv : (((p : ℕ) : ↥(modularFunctionFieldFull p)) ^ 12)⁻¹ ∈ W₀ := by
    have := W₀.mul_mem _ _ hmem hu.2
    rwa [mul_inv_rev, inv_inv, mul_assoc, mul_left_comm, mul_inv_cancel₀ hu0, mul_one] at this
  have hle : W₀.valuation ((((p : ℕ) : ↥(modularFunctionFieldFull p)) ^ 12)⁻¹) ≤ 1 := (W₀.valuation_le_one_iff _).mpr hinv
  rw [map_inv₀, map_pow, inv_le_one₀ (pow_pos (zero_lt_iff.mpr ?_) _)] at hle
  · exact absurd (pow_lt_one₀ zero_le' hp₀ (by norm_num)) (not_lt.mpr hle)
  · rw [ne_eq, map_eq_zero]; exact hpF

end Unit
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

section Main

variable (p : ℕ) [hp : Fact p.Prime] [NeZero p]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isReduced_and_natCard_primeSpectrum_crossing (hp5 : 5 ≤ p)
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits) (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits) (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p), ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (𝔭₀ 𝔭₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (h𝔭₀ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔭₀ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits))
    (h𝔭₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits))
    (e₀ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₀) ≃+* (ZMod p)[X])
    (he₀j : e₀ (Ideal.Quotient.mk 𝔭₀
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X)
    (he₀jp : e₀ (Ideal.Quotient.mk 𝔭₀ jp) = X ^ p)
    (e₁ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+* (ZMod p)[X])
    (he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X)
    (he₁j : e₁ (Ideal.Quotient.mk 𝔭₁
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X ^ p)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (ZMod p) κ] :
    IsReduced ((↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ⧸
        (𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := κ)) ⊔
         𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := κ)))) ∧
    Nat.card (PrimeSpectrum ((↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊗[ℤ] κ) ⧸
        (𝔭₀.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := κ)) ⊔
         𝔭₁.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (B := κ)))))
      = Nat.card ↥(ssJSet p κ) := by
  classical

  haveI : Algebra.FiniteType ℤ ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := (IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf p).1
  haveI : IsNoetherianRing ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsIntegrallyClosed ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
    TwoChartIntegralModel.isIntegrallyClosed_chartAlg ℤ ↥(modularFunctionFieldFull p) {IgusaScheme.jFull p}

  have hM := ModularCurve.DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair p jp hjp
    W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
  haveI : 𝔭₀.IsPrime := ((hM 𝔭₀).mpr (Or.inl h𝔭₀)).1.1
  haveI : 𝔭₁.IsPrime := ((hM 𝔭₁).mpr (Or.inr h𝔭₁)).1.1
  have hpinf : ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ∈ 𝔭₀ := (h𝔭₀ _).mpr (by simpa using hp₀)
  have hcover : ∀ 𝔮 : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), 𝔮.IsPrime → ((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ∈ 𝔮 → 𝔭₀ ≤ 𝔮 ∨ 𝔭₁ ≤ 𝔮 := by
    intro 𝔮 h𝔮 hp𝔮
    obtain ⟨𝔯, h𝔯, h𝔯le⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))})
      (J := 𝔮) ((Ideal.span_singleton_le_iff_mem _).mpr hp𝔮)
    rcases (hM 𝔯).mp h𝔯 with h | h
    · exact Or.inl ((le_of_eq (Ideal.ext fun a => (h𝔭₀ a).trans (h a).symm)).trans h𝔯le)
    · exact Or.inr ((le_of_eq (Ideal.ext fun a => (h𝔭₁ a).trans (h a).symm)).trans h𝔯le)

  obtain ⟨hW₀g, σ, hσj, hσjp, -, hW₁σ⟩ :=
    ModularCurve.DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap p jp hjp W₀ W₁ hp₀ hp₁
      hne hgen hcomplete ht

  have hu := uF_mem_and_inv_mem_of_gauss p hp5 W₀ hW₀g
  have huinf : uA p ∉ 𝔭₀ := fun h => by
    have h1 := (h𝔭₀ _).mp h
    rw [coe_uA, ValuationSubring.mem_nonunits_iff] at h1
    have h2 := (W₀.valuation_le_one_iff _).mpr hu.2
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (uF_ne_zero p)))] at h2
    exact absurd h1 (not_lt.mpr h2)
  have huzero : uA p ∈ 𝔭₁ :=
    (h𝔭₁ _).mpr (uF_mem_nonunits_of_swap p W₀ W₁ hp₀ hu jp hjp σ hσj hσjp hW₁σ)

  have hφ : algebraMap (ZMod p) κ = ZMod.castHom (dvd_refl p) κ := Subsingleton.elim _ _
  have hθj : BranchData.θpoly p κ (IgusaScheme.jFull p) 𝔭₀ e₀
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊗ₜ 1) = X := by
    rw [BranchData.θpoly_tmul_one, he₀j, Polynomial.map_X]
  have hθjp : BranchData.θpoly p κ (IgusaScheme.jFull p) 𝔭₀ e₀ (jp ⊗ₜ 1) = X ^ p := by
    rw [BranchData.θpoly_tmul_one, he₀jp, Polynomial.map_pow, Polynomial.map_X]
  have hrel : TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) - jp ^ p ∈ 𝔭₁ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply e₁.injective
    rw [map_sub, map_pow, map_sub, map_pow, he₁j, he₁jp, map_zero, sub_self]

  set S : Finset κ := (ssJSet_finite p κ).toFinset with hSdef
  have hS : ∀ a, a ∈ S ↔ a ∈ ssJSet p κ := fun a => Set.Finite.mem_toFinset _
  have hres := ModularCurve.DRModel.map_ringEquiv_quotient_chartAlgFin_modularUnit_eq_prod_ssJSet p hp5 W₀
    hW₀g 𝔭₀ h𝔭₀ e₀ he₀j (uA p) rfl κ S hS
  have hθu : BranchData.θpoly p κ (IgusaScheme.jFull p) 𝔭₀ e₀ (uA p ⊗ₜ 1) =
      Polynomial.C 1 * ∏ a ∈ S, (X - Polynomial.C a) ^ (12 / jWidth a) := by
    rw [BranchData.θpoly_tmul_one, hφ, hres, map_one, one_mul]
  have hn : ∀ a ∈ S, 0 < 12 / jWidth a := fun a _ =>
    Nat.div_pos ((Nat.le_of_dvd (by norm_num) (jWidth_dvd_six a)).trans (by norm_num)) (jWidth_pos a)

  obtain ⟨hred, hcard⟩ :=
    Ideal.isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness p
      ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) 𝔭₀ 𝔭₁ hpinf hcover (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) jp (uA p) (vA p)
      (uA_mul_vA p) huzero huinf κ (BranchData.θpoly p κ (IgusaScheme.jFull p) 𝔭₀ e₀)
      (BranchData.θpoly_surjective p κ (IgusaScheme.jFull p) 𝔭₀ e₀)
      (BranchData.ker_θpoly p κ (IgusaScheme.jFull p) 𝔭₀ e₀) hθj hθjp hrel S (fun a => 12 / jWidth a) hn
      1 one_ne_zero hθu
  refine ⟨hred, hcard.trans ?_⟩
  rw [hSdef, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (ssJSet_finite p κ)]

end Main
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData"

end CrossingFin
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry ModularCurve AlgebraicCurve"
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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

section C1Holes

p2m_open "AlgebraicCurve.TwoChartIntegralModel"

theorem Cert.isReduced_pullback_es
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
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
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (ZMod p) κ]
    (𝒞 : Cert p κ jp W₀ W₁) :
    IsReduced (pullback (GLUECI.es 𝒞.Dinf) (GLUECI.es 𝒞.Dzero)) := by
  obtain ⟨hred, -⟩ := CrossingFin.isReduced_and_natCard_primeSpectrum_crossing p hp jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
      𝒞.𝔭₀ 𝒞.𝔭₁ 𝒞.h𝔭₀ 𝒞.h𝔭₁ 𝒞.e₀ 𝒞.he₀j 𝒞.he₀jp 𝒞.e₁ 𝒞.he₁jp 𝒞.he₁j κ
  obtain ⟨-, a₀, a₁, c, ha₀, ha₁, hsum⟩ := ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair p jp hjp W₀ W₁
      hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ 𝒞.𝔭₁ 𝒞.h𝔭₁ 𝒞.e₁ 𝒞.he₁jp 𝒞.he₁j
  exact GLUECI.isReduced_pullback_es_of_map 𝒞.Dinf 𝒞.Dzero 𝒞.hKF₀ 𝒞.hKF₁ 𝒞.hKI₀ 𝒞.hKI₁ ((𝒞.h𝔮₀ a₀).mpr ha₀)
    ((𝒞.h𝔮₁ a₁).mpr ha₁) hsum hred

theorem Cert.natCard_pullback_es
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
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
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (ZMod p) κ]
    (𝒞 : Cert p κ jp W₀ W₁) :
    Nat.card ↥(pullback (GLUECI.es 𝒞.Dinf) (GLUECI.es 𝒞.Dzero)) = Nat.card ↥(ssJSet p κ) := by
  obtain ⟨-, hcard⟩ := CrossingFin.isReduced_and_natCard_primeSpectrum_crossing p hp jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
      𝒞.𝔭₀ 𝒞.𝔭₁ 𝒞.h𝔭₀ 𝒞.h𝔭₁ 𝒞.e₀ 𝒞.he₀j 𝒞.he₀jp 𝒞.e₁ 𝒞.he₁jp 𝒞.he₁j κ
  obtain ⟨-, a₀, a₁, c, ha₀, ha₁, hsum⟩ := ModularCurve.DRModel.exists_chartAlgInf_residue_eq_inv_and_cusps_separate_of_valuationSubring_pair p jp hjp W₀ W₁
      hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ 𝒞.𝔭₁ 𝒞.h𝔭₁ 𝒞.e₁ 𝒞.he₁jp 𝒞.he₁j
  exact GLUECI.natCard_pullback_es_of_map 𝒞.Dinf 𝒞.Dzero 𝒞.hKF₀ 𝒞.hKF₁ 𝒞.hKI₀ 𝒞.hKI₁ ((𝒞.h𝔮₀ a₀).mpr ha₀)
    ((𝒞.h𝔮₁ a₁).mpr ha₁) hsum hcard

theorem Cert.sec
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
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (ZMod p) κ]
    (𝒞 : Cert p κ jp W₀ W₁) :
    (∀ (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
         (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)),
         ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
                 TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) →
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range (GLUECI.es 𝒞.Dinf).base) ∧
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range (GLUECI.es 𝒞.Dzero).base) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range (GLUECI.es 𝒞.Dzero).base)) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range (GLUECI.es 𝒞.Dinf).base))) := by
  intro ψ ε hε
  have hχ : ∀ (a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (c : κ), (GLUECI.secChar κ ψ).toRingHom (a ⊗ₜ[ℤ] c) = (ψ a : κ) * c := fun a c => by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, GLUECI.secChar_tmul, eq_intCast]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine (GLUECI.range_sectionFibre_subset_range_es_iff p 𝒞.Dinf ψ ε hε).mpr ?_
    rw [𝒞.hKI₀]
    exact C1Glue.map_le_ker_of_char κ p ψ (GLUECI.secChar κ ψ).toRingHom hχ 𝒞.𝔮₀ (fun a ha => h a ((𝒞.h𝔮₀ a).mp ha))
  · refine (GLUECI.range_sectionFibre_subset_range_es_iff p 𝒞.Dzero ψ ε hε).mpr ?_
    rw [𝒞.hKI₁]
    exact C1Glue.map_le_ker_of_char κ p ψ (GLUECI.secChar κ ψ).toRingHom hχ 𝒞.𝔮₁ (fun a ha => h a ((𝒞.h𝔮₁ a).mp ha))
  · refine GLUECI.disjoint_range_sectionFibre_range_es p 𝒞.Dzero ψ ε hε ?_
    rw [𝒞.hKI₁]
    refine C1Glue.not_map_le_ker_of_char κ p ψ (GLUECI.secChar κ ψ).toRingHom hχ 𝒞.𝔮₁ ?_
    obtain ⟨a, ha, hna⟩ := h
    exact ⟨a, (𝒞.h𝔮₁ a).mpr ha, hna⟩
  · refine GLUECI.disjoint_range_sectionFibre_range_es p 𝒞.Dinf ψ ε hε ?_
    rw [𝒞.hKI₀]
    refine C1Glue.not_map_le_ker_of_char κ p ψ (GLUECI.secChar κ ψ).toRingHom hχ 𝒞.𝔮₀ ?_
    obtain ⟨a, ha, hna⟩ := h
    exact ⟨a, (𝒞.h𝔮₀ a).mpr ha, hna⟩

end C1Holes
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

section IsoTransport

variable {X Y Y' : Scheme.{u}}

def pullbackIsoComp (e : Y' ≅ Y) (f g : Y ⟶ X) : pullback (e.hom ≫ f) (e.hom ≫ g) ≅ pullback f g :=
  asIso (pullback.map (e.hom ≫ f) (e.hom ≫ g) f g e.hom e.hom (𝟙 X) (by rw [Category.comp_id]) (by rw [Category.comp_id]))

theorem isReduced_pullback_iso_comp (e : Y' ≅ Y) (f g : Y ⟶ X) [IsReduced (pullback f g)] :
    IsReduced (pullback (e.hom ≫ f) (e.hom ≫ g)) :=
  isReduced_of_isOpenImmersion (pullbackIsoComp e f g).hom

theorem natCard_pullback_iso_comp (e : Y' ≅ Y) (f g : Y ⟶ X) :
    Nat.card ↥(pullback (e.hom ≫ f) (e.hom ≫ g)) = Nat.card ↥(pullback f g) :=
  Nat.card_congr (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (pullbackIsoComp e f g))).toEquiv

end IsoTransport
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

section C1Assembly

p2m_open "AlgebraicCurve.TwoChartIntegralModel"

theorem c1plus
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
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
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] :
    ∃ (M : CurveModel κ (RatFunc κ))
      (cInf cZero : M.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      cInf ≫ pullback.snd _ _ = M.toBase ∧ cZero ≫ pullback.snd _ _ = M.toBase ∧
      IsClosedImmersion cInf ∧ IsClosedImmersion cZero ∧
      (∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
          x ∈ Set.range cInf.base ∨ x ∈ Set.range cZero.base) ∧
      Set.range cInf.base ≠ Set.range cZero.base ∧
      IsReduced (pullback cInf cZero) ∧
      Nat.card ↥(pullback cInf cZero) = Nat.card ↥(ssJSet p κ) ∧
      (∀ (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
         (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)),
         ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
                 TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) →
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range cInf.base) ∧
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range cZero.base) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range cZero.base)) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range cInf.base))) := by
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  obtain ⟨𝒞⟩ := nonempty_cert p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ κ

  obtain ⟨M, e, he⟩ := AlgebraicCurve.CurveModel.exists_curveModel_ratFunc κ
  haveI := GLUECI.isClosedImmersion_es 𝒞.Dinf
  haveI := GLUECI.isClosedImmersion_es 𝒞.Dzero
  haveI hR := Cert.isReduced_pullback_es p hp jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ κ 𝒞
  have hN := Cert.natCard_pullback_es p hp jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ κ 𝒞
  have hS := Cert.sec p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ κ 𝒞
  have hrInf : Set.range (e.hom ≫ GLUECI.es 𝒞.Dinf).base = Set.range (GLUECI.es 𝒞.Dinf).base := range_iso_hom_comp e _
  have hrZero : Set.range (e.hom ≫ GLUECI.es 𝒞.Dzero).base = Set.range (GLUECI.es 𝒞.Dzero).base := range_iso_hom_comp e _
  refine ⟨M, e.hom ≫ GLUECI.es 𝒞.Dinf, e.hom ≫ GLUECI.es 𝒞.Dzero, ?_, ?_, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact (congrArg (e.hom ≫ ·) (GLUECI.es_snd 𝒞.Dinf)).trans he
  · rw [Category.assoc]; exact (congrArg (e.hom ≫ ·) (GLUECI.es_snd 𝒞.Dzero)).trans he
  · intro x; rw [hrInf, hrZero]; exact 𝒞.cover x
  · rw [hrInf, hrZero]; exact 𝒞.range_ne
  · exact isReduced_pullback_iso_comp e _ _
  · rw [natCard_pullback_iso_comp]; exact hN
  · intro ψ ε hε
    rw [hrInf, hrZero]
    exact hS ψ ε hε

end C1Assembly
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

end TwoLinesAsm
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.GLUECI P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry.Spec P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.AlgebraicGeometry P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.TensorAdapt P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.BranchData P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators.CrossingFin"

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p)
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
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] :
    ∃ (M : CurveModel κ (RatFunc κ))
      (cInf cZero : M.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      cInf ≫ pullback.snd _ _ = M.toBase ∧ cZero ≫ pullback.snd _ _ = M.toBase ∧
      IsClosedImmersion cInf ∧ IsClosedImmersion cZero ∧
      (∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
          x ∈ Set.range cInf.base ∨ x ∈ Set.range cZero.base) ∧
      Set.range cInf.base ≠ Set.range cZero.base ∧
      IsReduced (pullback cInf cZero) ∧
      Nat.card ↥(pullback cInf cZero) = Nat.card ↥(ssJSet p κ) ∧
      (∀ (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
         (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)),
         ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
                 TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) →
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range cInf.base) ∧
         ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ a) →
            Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range cZero.base) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range cZero.base)) ∧
         ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
              (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
            Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range cInf.base))) :=
  TwoLinesAsm.c1plus p hp jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ κ

end S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
end P2MW
export P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators (solution)
