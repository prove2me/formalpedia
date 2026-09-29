-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b745986d-2145-576b-9fd6-29e7e04ed5b6

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst_levelOne
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_forall_ord_nonneg
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_smul_mem_integers_of_isGoodDiv_of_admissible_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~isCurveOver_modularFunctionFieldBar~nodePairsOf ModularCurve.PlaceSpecialization~IsInftySide~LevelOneProlongationPair~IsCuspidal~IsZeroSide~IsCuspidal'~IsStrictTypeOne~redSnd~redFst Polynomial IsDedekindDomain"
open scoped Polynomial

namespace Ws28
namespace CoreOne

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap' {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hc' : algebraMap K F c ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ hc'),
      Subtype.ext (by simpa using inv_mul_cancel₀ hc')⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_algebraMap_mul {c : K} (hc : c ≠ 0) (x : F) :
    v.ord (algebraMap K F c * x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx, ord_algebraMap' v hc, zero_add]

theorem ord_smul {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rw [Algebra.smul_def]; exact ord_algebraMap_mul v hc x

theorem ord_neg (x : F) : v.ord (-x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : (-x) = algebraMap K F (-1) * x := by simp
    rw [h, ord_algebraMap_mul v (by norm_num) x]

theorem min_ord_le_ord_add {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (v.ord x) (v.ord y) ≤ v.ord (x + y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  set m := min (v.ord x) (v.ord y) with hm
  have hmem : ∀ z : F, z ≠ 0 → m ≤ v.ord z → z * (π : F) ^ (-m) ∈ v.toValuationSubring := by
    intro z hz hmz
    rw [v.mem_iff_ord_nonneg (mul_ne_zero hz (zpow_ne_zero _ hπF)), v.ord_mul hz (zpow_ne_zero _ hπF),
      v.ord_zpow, v.ord_coe_irreducible hπ, mul_one]
    omega
  have hsum : (x + y) * (π : F) ^ (-m) ∈ v.toValuationSubring := by
    rw [add_mul]; exact add_mem (hmem x hx (min_le_left _ _)) (hmem y hy (min_le_right _ _))
  have h := v.ord_nonneg_of_mem hsum
  rw [v.ord_mul hxy (zpow_ne_zero _ hπF), v.ord_zpow, v.ord_coe_irreducible hπ, mul_one] at h
  omega

theorem ord_add_eq_of_lt {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hlt : v.ord x < v.ord y) :
    v.ord (x + y) = v.ord x := by
  have hxy : x + y ≠ 0 := by
    intro h
    have : x = -y := eq_neg_of_add_eq_zero_left h
    rw [this, ord_neg] at hlt; exact lt_irrefl _ hlt
  have h1 := min_ord_le_ord_add v hx hy hxy
  have h2 := min_ord_le_ord_add v hxy (neg_ne_zero.mpr hy) (by simpa using hx)
  rw [ord_neg, add_neg_cancel_right] at h2
  omega

theorem mem_of_ord_nonneg' {x : F} (h : 0 ≤ v.ord x) : x ∈ v.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  · exact v.mem_of_ord_nonneg hx h

theorem ord_nonneg_of_ord_add_algebraMap_nonneg {x : F} (c : K)
    (h : 0 ≤ v.ord (algebraMap K F c + x)) : 0 ≤ v.ord x := by
  have hmem := mem_of_ord_nonneg' v h
  have : x = (algebraMap K F c + x) - algebraMap K F c := by ring
  rw [this]
  exact v.ord_nonneg_of_mem (sub_mem hmem (v.algebraMap_mem' c))

theorem HasValue.add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem HasValue.smul {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]; exact (v.hasValue_algebraMap c).mul h

theorem hasValue_zero : v.HasValue (0 : F) 0 := by
  simpa using v.hasValue_algebraMap (0 : K)

theorem eq_of_hasValue_algebraMap {c a : K} (h : v.HasValue (algebraMap K F c) a) : a = c :=
  h.unique (v.hasValue_algebraMap c)

theorem ord_nonneg_of_hasValue {g : F} {a : K} (h : v.HasValue g a) : 0 ≤ v.ord g :=
  v.ord_nonneg_of_mem h.mem

theorem ord_sub_pos_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (hne : g - algebraMap K F a ≠ 0) :
    0 < v.ord (g - algebraMap K F a) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' a)
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := rfl
    rw [this, map_sub, hres, sub_eq_zero]
    rfl
  have h0 := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hpos | h0
  · exact hpos
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hne hπ
    rw [← h0, zpow_zero, mul_one] at hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this]; exact Units.isUnit u

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hne : g ≠ 0) : 0 < v.ord g := by
  have := ord_sub_pos_of_hasValue v h (by simpa using hne)
  simpa using this

theorem mapDomain_apply_nonneg {ι κ : Type*} (f : ι → κ) (D : ι →₀ ℤ) (v : κ)
    (h : ∀ i, f i = v → 0 ≤ D i) : 0 ≤ Finsupp.mapDomain f D v := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Finsupp.single_apply]
  split_ifs with hi
  · exact h i hi
  · exact le_rfl

theorem mapDomain_apply_eq_zero {ι κ : Type*} (f : ι → κ) (D : ι →₀ ℤ) (v : κ)
    (h : ∀ i, f i = v → D i = 0) : Finsupp.mapDomain f D v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Finsupp.single_apply]
  split_ifs with hi
  · exact h i hi
  · rfl

theorem inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S) (hu : IsUnit (⟨x, hx⟩ : S)) :
    x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact SetLike.coe_mem _

theorem le_ord_sub_algebraMap {x : F} (c : K) {m : ℤ} (hm : m ≤ 0) (hx : m ≤ v.ord x)
    (hne : x - algebraMap K F c ≠ 0) : m ≤ v.ord (x - algebraMap K F c) := by
  by_cases hc : c = 0
  · simpa [hc] using hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_sub, ord_neg, ord_algebraMap' v hc]; exact hm
  have hy : -algebraMap K F c ≠ 0 := neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr hc)
  have hxy : x + -algebraMap K F c ≠ 0 := by rwa [← sub_eq_add_neg]
  have h := min_ord_le_ord_add v hx0 hy hxy
  rw [← sub_eq_add_neg, ord_neg, ord_algebraMap' v hc] at h
  exact le_trans (le_min hx hm) h

end PlaceHelpers

section Curve
open IntermediateField

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

def gens : Set (LaurentSeries L) := ⇑(coeffEmb L) '' divisorExpansions N

theorem adjoin_gens_le : adjoin L (gens L N) ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
  change adjoin L (gens L N) ≤ adjoin L _
  refine adjoin.mono L _ _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, IntermediateField.subset_adjoin ℚ _ hx, rfl⟩

theorem laurentBaseChange_le_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) ≤ adjoin L (gens L N) := by
  change adjoin L _ ≤ adjoin L (gens L N)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gens L N)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gens L N)).algebraMap_mem _
  · exact IntermediateField.subset_adjoin L _ ⟨z, hz, rfl⟩

theorem laurentBaseChange_eq_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) = adjoin L (gens L N) :=
  le_antisymm (laurentBaseChange_le_adjoin_gens L N) (adjoin_gens_le L N)

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  rw [coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]

theorem gens_eq_divisorExpansionsC : gens L N = divisorExpansionsC L N := by
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩
    exact ⟨d, hd, hdN, coeffEmb_qExpand_jq L d⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact ⟨_, ⟨d, hd, hdN, rfl⟩, coeffEmb_qExpand_jq L d⟩

theorem laurentBaseChange_eq_fullC :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldFullC L N := by
  rw [laurentBaseChange_eq_adjoin_gens, gens_eq_divisorExpansionsC]; rfl

theorem isCurveOver_modularFunctionFieldBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := by
  rw [show modularFunctionFieldBar N = modularFunctionFieldFullC (AlgebraicClosure ℚ) N from
    laurentBaseChange_eq_fullC (AlgebraicClosure ℚ) N]
  exact ModularCurve.isCurveOver_modularFunctionFieldFullC (AlgebraicClosure ℚ) N

private theorem _root_.Ws28.CoreOne.exists_divisor (f : ↥(modularFunctionFieldBar N)) (hf : f ≠ 0) :
    ∃ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), ∀ W, D W = W.ord f := by
  have h : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    (isCurveOver_modularFunctionFieldBar N).toHasPrincipalDivisors
  obtain ⟨D, hD, -⟩ := h.exists_divisor f hf
  exact ⟨D, hD⟩

p2m_export "Ws28.CoreOne" "exists_divisor"
end Curve

section Tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.ProlongationTuple)

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "Fb" => modularFunctionFieldC k 1
local notation "cst" => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "cstb" => algebraMap k (modularFunctionFieldC k 1)
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

theorem red_eq_redBar (R : P.ProlongationTuple) (a : A) : red a = R.redBar (IsLocalRing.residue A a) := (R.redBar_residue a).symm

theorem isUnit_of_red_ne_zero (R : P.ProlongationTuple) {a : A} (h : red a ≠ 0) : IsUnit a := by
  rw [red_eq_redBar R] at h
  have : IsLocalRing.residue A a ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp this

theorem cst_mem₁ (a : A) : cst (a : QQ) ∈ R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr a.2
theorem cst_mem₂ (a : A) : cst (a : QQ) ∈ R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr a.2

theorem smul_mem₁ {f : FF} (hf : f ∈ R.R₁.integers) (a : A) : (a : QQ) • f ∈ R.R₁.integers := by
  rw [Algebra.smul_def]; exact mul_mem (cst_mem₁ R a) hf
theorem smul_mem₂ {f : FF} (hf : f ∈ R.R₂.integers) (a : A) : (a : QQ) • f ∈ R.R₂.integers := by
  rw [Algebra.smul_def]; exact mul_mem (cst_mem₂ R a) hf

theorem residue₁_ne_zero_iff {f : R.R₁.integers} : R.residue₁ f ≠ 0 ↔ R.R₁.residue f ≠ 0 := by
  rw [R.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective)
theorem residue₂_ne_zero_iff {f : R.R₂.integers} : R.residue₂ f ≠ 0 ↔ R.R₂.residue f ≠ 0 := by
  rw [R.residue₂_apply]; exact (map_ne_zero_iff _ R.ι.injective)

theorem residue₁_cst (a : A) : R.residue₁ ⟨cst (a : QQ), cst_mem₁ R a⟩ = cstb (red a) := by
  apply Subtype.ext
  rw [R.residue₁_apply, R.ι_coe]
  have h1 : R.R₁.residue ⟨cst (a : QQ), cst_mem₁ R a⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a) :=
    R.R₁.residue_algebraMap a
  rw [h1]
  have hl : ((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a) :
      ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A a) := by
    rfl
  have hr : ((cstb (red a) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
      algebraMap k (LaurentSeries k) (red a) := by
    rfl
  rw [hl, hr, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single,
    R.redBar_residue]
theorem residue₂_cst (a : A) : R.residue₂ ⟨cst (a : QQ), cst_mem₂ R a⟩ = cstb (red a) := by
  apply Subtype.ext
  rw [R.residue₂_apply, R.ι_coe]
  have h1 : R.R₂.residue ⟨cst (a : QQ), cst_mem₂ R a⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a) :=
    R.R₂.residue_algebraMap a
  rw [h1]
  have hl : ((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a) :
      ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A a) := by
    rfl
  have hr : ((cstb (red a) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
      algebraMap k (LaurentSeries k) (red a) := by
    rfl
  rw [hl, hr, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single,
    R.redBar_residue]

theorem residue₁_smul (a : A) {f : FF} (hf : f ∈ R.R₁.integers) :
    R.residue₁ ⟨(a : QQ) • f, smul_mem₁ R hf a⟩ = red a • R.residue₁ ⟨f, hf⟩ := by
  have : (⟨(a : QQ) • f, smul_mem₁ R hf a⟩ : R.R₁.integers) = ⟨cst (a : QQ), cst_mem₁ R a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def _ _)
  rw [this, map_mul, residue₁_cst, Algebra.smul_def]
theorem residue₂_smul (a : A) {f : FF} (hf : f ∈ R.R₂.integers) :
    R.residue₂ ⟨(a : QQ) • f, smul_mem₂ R hf a⟩ = red a • R.residue₂ ⟨f, hf⟩ := by
  have : (⟨(a : QQ) • f, smul_mem₂ R hf a⟩ : R.R₂.integers) = ⟨cst (a : QQ), cst_mem₂ R a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def _ _)
  rw [this, map_mul, residue₂_cst, Algebra.smul_def]

theorem not_isStrictSnd_of_isStrictFst {W : Place QQ FF} (h : P.IsStrictFst W) : ¬ P.IsStrictSnd W := by
  rintro ⟨h1, h2⟩
  apply h.2
  rw [h.1, ← h1]

theorem reduceFst_ne_of_fixed {v : Place k Fb} (hv : φ (φ v) = v) {W : Place QQ FF}
    (hW : P.IsStrictFst W ∨ P.IsStrictSnd W) : P.reduceFst W ≠ v := by
  rintro rfl
  rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 hv
  ·
    apply h2
    apply frobOnPlacesGeomLevel_injective k 1 data hKr
    rw [← h1]; exact hv
theorem reduceSnd_ne_of_fixed {v : Place k Fb} (hv : φ (φ v) = v) {W : Place QQ FF}
    (hW : P.IsStrictFst W ∨ P.IsStrictSnd W) : P.reduceSnd W ≠ v := by
  rintro rfl
  rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply h2
    apply frobOnPlacesGeomLevel_injective k 1 data hKr
    rw [h1]; exact hv
  · exact h2 hv

end Tuple

section Faces

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "Fb" => modularFunctionFieldC k 1
local notation "cst" => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "cstb" => algebraMap k (modularFunctionFieldC k 1)
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

theorem F_LFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictFst Q) (hQ' : P.IsStrictFst Q') (hQQ' : P.reduceFst Q' = P.reduceFst Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k 1 (P.reduceFst Q))
    (hqN : ¬ q ∣ 1)
    (a : k) (ha : (P.reduceFst Q).evalAt (jGeomGen k 1) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₁ : g ∈ R.R₁.integers) (hg₁' : R.R₁.residue ⟨g, hg₁⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictFst W → P.reduceFst W = P.reduceFst Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₁ : ε ∈ R.R₁.integers) (hε₁' : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceFst Q).ord (R.residue₁ ⟨ε, hε₁⟩) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
    hR hQ hQ' hQQ' hne hQaff a ha h0 h1728 n hn g hg₁ hg₁' hgQ hgQ' hg0 e ε hε₁ hε₁' hgε

theorem F_LSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q') (hQQ' : P.reduceSnd Q' = P.reduceSnd Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k 1 (P.reduceSnd Q))
    (hqN : ¬ q ∣ 1)
    (a : k) (ha : (P.reduceSnd Q).evalAt (jGeomGen k 1) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₂ : g ∈ R.R₂.integers) (hg₂' : R.R₂.residue ⟨g, hg₂⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₂ : ε ∈ R.R₂.integers) (hε₂' : R.R₂.residue ⟨ε, hε₂⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceSnd Q).ord (R.residue₂ ⟨ε, hε₂⟩) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
    hR hQ hQ' hQQ' hne hQaff a ha h0 h1728 n hn g hg₂ hg₂' hgQ hgQ' hg0 e ε hε₂ hε₂' hgε

theorem not_side_of_affine (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place QQ FF)
    (h₁ : IsAffineGeomPlace k 1 (P.reduceFst W)) (h₂ : IsAffineGeomPlace k 1 (P.reduceSnd W)) :
    ¬ ProlongationTuple.IsInftySide P W ∧ ¬ ProlongationTuple.IsZeroSide P W := by
  constructor
  · intro h
    exact ModularCurve.PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P W h.1 h₁
  · intro h
    obtain ⟨a, ha, -⟩ :=
      ModularCurve.PlaceSpecialization.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd P W h₂
    exact absurd (h.1 a) (not_le.mpr ha)
theorem affine_both_of_strict (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place QQ FF)
    (h : (P.IsStrictFst W ∧ IsAffineGeomPlace k 1 (P.reduceFst W)) ∨ (P.IsStrictSnd W ∧ IsAffineGeomPlace k 1 (P.reduceSnd W))) :
    IsAffineGeomPlace k 1 (P.reduceFst W) ∧ IsAffineGeomPlace k 1 (P.reduceSnd W) := by
  rcases h with ⟨hs, ha⟩ | ⟨hs, ha⟩
  · refine ⟨ha, ?_⟩
    rw [← hs.1]; exact ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr _ ha
  · refine ⟨?_, ha⟩
    rw [hs.1]; exact ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr _ ha

theorem F_affine_frob (v : Place k Fb) (hv : IsAffineGeomPlace k 1 v) : IsAffineGeomPlace k 1 (φ v) :=
  ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr v hv

theorem F_cuspCoverFst (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (hqN : ¬ q ∣ 1)
    (v : Place k Fb) (hv : ¬ IsAffineGeomPlace k 1 v) :
    ∃ c : Place QQ FF, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v :=
  (ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
    hqN P v hv).1
theorem F_cuspCoverSnd (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (hqN : ¬ q ∣ 1)
    (v : Place k Fb) (hv : ¬ IsAffineGeomPlace k 1 v) :
    ∃ c : Place QQ FF, ProlongationTuple.IsZeroSide P c ∧ P.reduceSnd c = v :=
  (ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
    hqN P v hv).2

theorem F_const (hqN : ¬ q ∣ 1) (h : Fb) (hreg : ∀ v : Place k Fb, 0 ≤ v.ord h) : ∃ c : k, h = cstb c :=
  ModularCurve.exists_eq_algebraMap_of_forall_ord_nonneg k 1 hqN h hreg

theorem F_K1
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)
    (hgood : P.IsGoodDiv D)
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W)) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h₁ : c • f ∈ R.R₁.integers) (h₂ : c • f ∈ R.R₂.integers),
      R.R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c • f, h₂⟩ ≠ 0 :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_smul_mem_integers_of_isGoodDiv_of_admissible_levelOne
    hR hW hRL f hf D hDf hgood hadm

theorem F_alpha {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : P.ProlongationTuple}
    (hR : R.IsModel) {Qs : Place QQ FF} (hQs : P.IsStrictFst Qs)
    (r : FF) (h₁ : r ∈ R.R₁.integers)
    (hr : ∀ V : Place QQ FF, P.IsStrictFst V → P.reduceFst V = P.reduceFst Qs → 0 ≤ V.ord r) :
    ∃ c : A, Qs.HasValue r (c : QQ) ∧ (P.reduceFst Qs).HasValue (R.residue₁ ⟨r, h₁⟩ : Fb) (red c) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_hasValue_of_mem_smoothLocalRingFst_levelOne hR hQs r h₁
    ((R.mem_smoothLocalRingFst_iff _ r).mpr ⟨h₁, fun W hW hWv => mem_of_ord_nonneg' W (hr W hW hWv)⟩)

theorem F_ss_fixed (hqN : ¬ q ∣ 1) (w : Place k Fb) (hw : w ∈ ssPlaces q 1 k) : φ (φ w) = w :=
  ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hqN data hKr w hw

theorem F_nodePair {W : Finset (Place k Fb)} (w : Place k Fb) (hw : w ∈ W) :
    (w, arithFrobC q k 1 • w) ∈ nodePairsOfPlaces (arithFrobC q k 1) W ∧ arithFrobC q k 1 • w = φ w :=
  ⟨smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k 1) hw,
    ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w⟩

theorem exists_mu (κ : k) : ∃ μ : A, red μ ≠ 0 ∧ red μ ≠ κ := by
  by_cases h1 : κ = 1
  · subst h1
    by_cases h2 : (2 : k) = 0
    ·
      obtain ⟨ζ, hζ⟩ : ∃ ζ : QQ, (X ^ 2 + X + 1 : QQ[X]).IsRoot ζ := by
        refine IsAlgClosed.exists_root _ ?_
        have hdeg : (X ^ 2 + X + 1 : QQ[X]).degree = 2 := by compute_degree!
        rw [hdeg]; norm_num
      have hζeq : ζ ^ 2 + ζ + 1 = 0 := by simpa using hζ
      have hζ3 : ζ ^ 3 = 1 := by
        have : ζ ^ 3 - 1 = (ζ - 1) * (ζ ^ 2 + ζ + 1) := by ring
        rw [hζeq, mul_zero, sub_eq_zero] at this; exact this
      have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζeq
      have hζA : ζ ∈ A := by
        rcases A.mem_or_inv_mem ζ with h | h
        · exact h
        · have : ζ = (ζ⁻¹) ^ 2 := by
            have h3 : ζ * ζ ^ 2 = 1 := by rw [← pow_succ', hζ3]
            rw [inv_pow]; exact eq_inv_of_mul_eq_one_left h3
          rw [this]; exact pow_mem h 2
      refine ⟨⟨ζ, hζA⟩, ?_, ?_⟩
      · intro h0
        have : red (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1) = 0 := by
          have hz : (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1 : A) = 0 := Subtype.ext (by simpa using hζeq)
          rw [hz, map_zero]
        rw [map_add, map_add, map_pow, h0, map_one] at this
        simp at this
      · intro h1
        have : red (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1) = 0 := by
          have hz : (⟨ζ, hζA⟩ ^ 2 + ⟨ζ, hζA⟩ + 1 : A) = 0 := Subtype.ext (by simpa using hζeq)
          rw [hz, map_zero]
        rw [map_add, map_add, map_pow, h1, map_one, one_pow] at this
        have h11 : (1 : k) + 1 = 0 := one_add_one_eq_two.trans h2
        rw [h11, zero_add] at this
        exact one_ne_zero this
    · refine ⟨-1, ?_, ?_⟩
      · rw [map_neg, map_one]; exact neg_ne_zero.mpr one_ne_zero
      · rw [map_neg, map_one]
        intro h
        apply h2
        linear_combination -h
  · exact ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; exact Ne.symm h1⟩

end Faces

section Main

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar (1 * q)
local notation "Fb" => modularFunctionFieldC k 1
local notation "cst" => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "cstb" => algebraMap k (modularFunctionFieldC k 1)
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

set_option maxHeartbeats 16000000 in
theorem core
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hNV : R.NodeValueLaw W) (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hQ₁j : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 1728)
    (hQ₂j : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 1728)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (n : ℕ) (hn : (n : k) ≠ 0) (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      V.ord f = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
  classical
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q 1 k := fun w hw => (hW w).mp hw
  set E₁ : Divisor QQ FF := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₁' : Divisor QQ FF := ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) with hE₁'
  set E₂ : Divisor QQ FF := ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  set E₂' : Divisor QQ FF := ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) with hE₂'
  set E : Divisor QQ FF := E₁' + E₂' with hE
  set E₀ : Divisor QQ FF := E₁ + E₂ with hE₀
  set D : Divisor QQ FF := (n : ℤ) • (E - E₀) with hD_def
  have hD : ∀ V, D V = V.ord f := fun V => by
    rw [hdiv V, hD_def, Finsupp.smul_apply, smul_eq_mul]

  have hQ₁inj : Function.Injective Q₁ := fun i j h => hinj₁ (by show P.reduceFst (Q₁ i) = P.reduceFst (Q₁ j); rw [h])
  have hQ₂inj : Function.Injective Q₂ := fun i j h => hinj₂ (by show P.reduceSnd (Q₂ i) = P.reduceSnd (Q₂ j); rw [h])
  have hQ₁'inj : Function.Injective Q₁' := fun i j h =>
    hinj₁ (by show P.reduceFst (Q₁ i) = P.reduceFst (Q₁ j); rw [← hred₁ i, ← hred₁ j, h])
  have hQ₂'inj : Function.Injective Q₂' := fun i j h =>
    hinj₂ (by show P.reduceSnd (Q₂ i) = P.reduceSnd (Q₂ j); rw [← hred₂ i, ← hred₂ j, h])

  have h12 : ∀ i j, Q₁ i ≠ Q₂ j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁ i) (h ▸ hQ₂ j)
  have h12' : ∀ i j, Q₁' i ≠ Q₂' j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁' i) (h ▸ hQ₂' j)
  have h1'2 : ∀ i j, Q₁' i ≠ Q₂ j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁' i) (h ▸ hQ₂ j)
  have h12'' : ∀ i j, Q₁ i ≠ Q₂' j := fun i j h => not_isStrictSnd_of_isStrictFst (hQ₁ i) (h ▸ hQ₂' j)

  have hE₁_apply : ∀ V, E₁ V = ∑ i, if Q₁ i = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₁, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₁'_apply : ∀ V, E₁' V = ∑ i, if Q₁' i = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₁', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₂_apply : ∀ V, E₂ V = ∑ j, if Q₂ j = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₂, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hE₂'_apply : ∀ V, E₂' V = ∑ j, if Q₂' j = V then (1 : ℤ) else 0 := fun V => by
    simp only [hE₂', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have hD_apply : ∀ V, D V = (n : ℤ) * ((E₁' V + E₂' V) - (E₁ V + E₂ V)) := fun V => by
    rw [hD_def, Finsupp.smul_apply, Finsupp.sub_apply, hE, hE₀, Finsupp.add_apply, Finsupp.add_apply, smul_eq_mul]

  have hE₁_off : ∀ V, (∀ i, V ≠ Q₁ i) → E₁ V = 0 := fun V h => by
    rw [hE₁_apply]; exact Finset.sum_eq_zero fun i _ => if_neg fun h' => h i h'.symm
  have hE₁'_off : ∀ V, (∀ i, V ≠ Q₁' i) → E₁' V = 0 := fun V h => by
    rw [hE₁'_apply]; exact Finset.sum_eq_zero fun i _ => if_neg fun h' => h i h'.symm
  have hE₂_off : ∀ V, (∀ j, V ≠ Q₂ j) → E₂ V = 0 := fun V h => by
    rw [hE₂_apply]; exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h j h'.symm
  have hE₂'_off : ∀ V, (∀ j, V ≠ Q₂' j) → E₂' V = 0 := fun V h => by
    rw [hE₂'_apply]; exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h j h'.symm

  have hsupp : ∀ V, D V ≠ 0 → ((∃ i, V = Q₁ i) ∨ (∃ i, V = Q₁' i)) ∨ ((∃ j, V = Q₂ j) ∨ (∃ j, V = Q₂' j)) := by
    intro V hV
    by_contra h; push Not at h
    apply hV
    rw [hD_apply, hE₁_off V h.1.1, hE₁'_off V h.1.2, hE₂_off V h.2.1, hE₂'_off V h.2.2]
    simp
  have htype : ∀ V, D V ≠ 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := by
    intro V hV
    rcases hsupp V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    exacts [Or.inl (hQ₁ i), Or.inl (hQ₁' i), Or.inr (hQ₂ j), Or.inr (hQ₂' j)]
  have hgood : P.IsGoodDiv D := fun V hV => htype V (Finsupp.mem_support_iff.mp hV)

  have hE₂_fst : ∀ V, P.IsStrictFst V → E₂ V = 0 := fun V hV =>
    hE₂_off V fun j h => not_isStrictSnd_of_isStrictFst hV (h ▸ hQ₂ j)
  have hE₂'_fst : ∀ V, P.IsStrictFst V → E₂' V = 0 := fun V hV =>
    hE₂'_off V fun j h => not_isStrictSnd_of_isStrictFst hV (h ▸ hQ₂' j)
  have hE₁_snd : ∀ V, P.IsStrictSnd V → E₁ V = 0 := fun V hV =>
    hE₁_off V fun i h => not_isStrictSnd_of_isStrictFst (h ▸ hQ₁ i) hV
  have hE₁'_snd : ∀ V, P.IsStrictSnd V → E₁' V = 0 := fun V hV =>
    hE₁'_off V fun i h => not_isStrictSnd_of_isStrictFst (h ▸ hQ₁' i) hV
  have hE₁_nfst : ∀ V, ¬ P.IsStrictFst V → E₁ V = 0 := fun V hV =>
    hE₁_off V fun i h => hV (h ▸ hQ₁ i)
  have hE₁'_nfst : ∀ V, ¬ P.IsStrictFst V → E₁' V = 0 := fun V hV =>
    hE₁'_off V fun i h => hV (h ▸ hQ₁' i)
  have hE₂_nsnd : ∀ V, ¬ P.IsStrictSnd V → E₂ V = 0 := fun V hV =>
    hE₂_off V fun j h => hV (h ▸ hQ₂ j)
  have hE₂'_nsnd : ∀ V, ¬ P.IsStrictSnd V → E₂' V = 0 := fun V hV =>
    hE₂'_off V fun j h => hV (h ▸ hQ₂' j)
  have hfst : P.fstDiv D = (n : ℤ) • (E₁' - E₁) := by
    ext V
    show (D.filter P.IsStrictFst) V = ((n : ℤ) • (E₁' - E₁)) V
    rw [Finsupp.filter_apply]
    by_cases hV : P.IsStrictFst V
    · rw [if_pos hV, hD_apply, hE₂_fst V hV, hE₂'_fst V hV]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]; ring
    · rw [if_neg hV]
      simp [Finsupp.smul_apply, Finsupp.sub_apply, hE₁_nfst V hV, hE₁'_nfst V hV]
  have hsnd : P.sndDiv D = (n : ℤ) • (E₂' - E₂) := by
    ext V
    show (D.filter P.IsStrictSnd) V = ((n : ℤ) • (E₂' - E₂)) V
    rw [Finsupp.filter_apply]
    by_cases hV : P.IsStrictSnd V
    · rw [if_pos hV, hD_apply, hE₁_snd V hV, hE₁'_snd V hV]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]; ring
    · rw [if_neg hV]
      simp [Finsupp.smul_apply, Finsupp.sub_apply, hE₂_nsnd V hV, hE₂'_nsnd V hV]

  have hmapE₁ : Finsupp.mapDomain P.reduceFst E₁' = Finsupp.mapDomain P.reduceFst E₁ := by
    show Finsupp.mapDomain.addMonoidHom P.reduceFst E₁' = Finsupp.mapDomain.addMonoidHom P.reduceFst E₁
    rw [hE₁', hE₁, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, hred₁ i]
  have hmapE₂ : Finsupp.mapDomain P.reduceSnd E₂' = Finsupp.mapDomain P.reduceSnd E₂ := by
    show Finsupp.mapDomain.addMonoidHom P.reduceSnd E₂' = Finsupp.mapDomain.addMonoidHom P.reduceSnd E₂
    rw [hE₂', hE₂, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, hred₂ j]
  have hmapFst : Finsupp.mapDomain P.reduceFst (P.fstDiv D) = 0 := by
    rw [hfst, Finsupp.mapDomain_smul, Finsupp.mapDomain_sub, hmapE₁, sub_self, smul_zero]
  have hmapSnd : Finsupp.mapDomain P.reduceSnd (P.sndDiv D) = 0 := by
    rw [hsnd, Finsupp.mapDomain_smul, Finsupp.mapDomain_sub, hmapE₂, sub_self, smul_zero]

  have hsum₁ : ∀ i, (∑ l, if Q₁ l = Q₁ i then (1 : ℤ) else 0) = 1 := fun i => by
    rw [Finset.sum_eq_single i (fun l _ hl => if_neg (fun h => hl (hQ₁inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hsum₁' : ∀ i, (∑ l, if Q₁' l = Q₁' i then (1 : ℤ) else 0) = 1 := fun i => by
    rw [Finset.sum_eq_single i (fun l _ hl => if_neg (fun h => hl (hQ₁'inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hsum₂ : ∀ j, (∑ l, if Q₂ l = Q₂ j then (1 : ℤ) else 0) = 1 := fun j => by
    rw [Finset.sum_eq_single j (fun l _ hl => if_neg (fun h => hl (hQ₂inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hsum₂' : ∀ j, (∑ l, if Q₂' l = Q₂' j then (1 : ℤ) else 0) = 1 := fun j => by
    rw [Finset.sum_eq_single j (fun l _ hl => if_neg (fun h => hl (hQ₂'inj h))) (fun h => (h (Finset.mem_univ _)).elim)]
    simp
  have hE₁Q₁ : ∀ i, E₁ (Q₁ i) = 1 := fun i => by rw [hE₁_apply, hsum₁]
  have hE₁'Q₁' : ∀ i, E₁' (Q₁' i) = 1 := fun i => by rw [hE₁'_apply, hsum₁']
  have hE₂Q₂ : ∀ j, E₂ (Q₂ j) = 1 := fun j => by rw [hE₂_apply, hsum₂]
  have hE₂'Q₂' : ∀ j, E₂' (Q₂' j) = 1 := fun j => by rw [hE₂'_apply, hsum₂']
  have hE₁'Q₁ : ∀ i, E₁' (Q₁ i) = if Q₁' i = Q₁ i then 1 else 0 := fun i => by
    rw [hE₁'_apply]
    by_cases h : Q₁' i = Q₁ i
    · rw [if_pos h, ← h, hsum₁']
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = i := hinj₁ (by show P.reduceFst (Q₁ l) = P.reduceFst (Q₁ i); rw [← hred₁ l, hl])
      subst this; exact h hl
  have hE₁Q₁' : ∀ i, E₁ (Q₁' i) = if Q₁' i = Q₁ i then 1 else 0 := fun i => by
    rw [hE₁_apply]
    by_cases h : Q₁' i = Q₁ i
    · rw [if_pos h, h, hsum₁]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = i := hinj₁ (by show P.reduceFst (Q₁ l) = P.reduceFst (Q₁ i); rw [hl, hred₁ i])
      subst this; exact h hl.symm
  have hE₂'Q₂ : ∀ j, E₂' (Q₂ j) = if Q₂' j = Q₂ j then 1 else 0 := fun j => by
    rw [hE₂'_apply]
    by_cases h : Q₂' j = Q₂ j
    · rw [if_pos h, ← h, hsum₂']
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = j := hinj₂ (by show P.reduceSnd (Q₂ l) = P.reduceSnd (Q₂ j); rw [← hred₂ l, hl])
      subst this; exact h hl
  have hE₂Q₂' : ∀ j, E₂ (Q₂' j) = if Q₂' j = Q₂ j then 1 else 0 := fun j => by
    rw [hE₂_apply]
    by_cases h : Q₂' j = Q₂ j
    · rw [if_pos h, h, hsum₂]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun l _ => if_neg fun hl => ?_
      have : l = j := hinj₂ (by show P.reduceSnd (Q₂ l) = P.reduceSnd (Q₂ j); rw [hl, hred₂ j])
      subst this; exact h hl.symm
  have hDQ₁ : ∀ i, D (Q₁ i) = if Q₁' i = Q₁ i then 0 else -(n : ℤ) := fun i => by
    rw [hD_apply, hE₂_fst _ (hQ₁ i), hE₂'_fst _ (hQ₁ i), hE₁Q₁, hE₁'Q₁]; split_ifs <;> ring
  have hDQ₁' : ∀ i, D (Q₁' i) = if Q₁' i = Q₁ i then 0 else (n : ℤ) := fun i => by
    rw [hD_apply, hE₂_fst _ (hQ₁' i), hE₂'_fst _ (hQ₁' i), hE₁'Q₁', hE₁Q₁']; split_ifs <;> ring
  have hDQ₂ : ∀ j, D (Q₂ j) = if Q₂' j = Q₂ j then 0 else -(n : ℤ) := fun j => by
    rw [hD_apply, hE₁_snd _ (hQ₂ j), hE₁'_snd _ (hQ₂ j), hE₂Q₂, hE₂'Q₂]; split_ifs <;> ring
  have hDQ₂' : ∀ j, D (Q₂' j) = if Q₂' j = Q₂ j then 0 else (n : ℤ) := fun j => by
    rw [hD_apply, hE₁_snd _ (hQ₂' j), hE₁'_snd _ (hQ₂' j), hE₂'Q₂', hE₂Q₂']; split_ifs <;> ring
  have hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D ∈
      GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W) := by
    have : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D = 0 := by
      unfold PlaceSpecialization.glueData
      rw [hmapFst, hmapSnd]; rfl
    rw [this]; exact zero_mem _

  obtain ⟨c, hc0, hf₁₁, hf₁₂, hr₁, hr₂⟩ := F_K1 hR hW hRL hNV f hf D hD hgood hadm
  set f₁ : FF := c • f with hf₁_def
  have hordf₁ : ∀ V : Place QQ FF, V.ord f₁ = V.ord f := fun V => ord_smul V hc0 f
  have hDf₁ : ∀ V, D V = V.ord f₁ := fun V => by rw [hordf₁, hD]
  have hpole_f₁ : ∀ V : Place QQ FF, V.ord f₁ < 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := fun V hV =>
    htype V (by rw [hDf₁]; exact hV.ne)

  have hnopole₁ : ∀ v : Place k Fb, φ (φ v) = v → ∀ V : Place QQ FF, P.reduceFst V = v → 0 ≤ V.ord f₁ := by
    intro v hv V hVv
    by_contra hlt; push Not at hlt
    exact reduceFst_ne_of_fixed hv (hpole_f₁ V hlt) hVv
  have hncusp : ∀ V : Place QQ FF, D V ≠ 0 →
      ¬ ProlongationTuple.IsInftySide P V ∧ ¬ ProlongationTuple.IsZeroSide P V := by
    intro V hV
    refine (fun h => not_side_of_affine P V h.1 h.2) (affine_both_of_strict P V ?_)
    rcases hsupp V hV with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨hQ₁ i, hT₁aff _ ((hT₁ _).mpr ⟨i, rfl⟩)⟩
    · exact Or.inl ⟨hQ₁' i, hT₁aff _ ((hT₁ _).mpr ⟨i, (hred₁ i).symm⟩)⟩
    · exact Or.inr ⟨hQ₂ j, hT₂aff _ ((hT₂ _).mpr ⟨j, rfl⟩)⟩
    · exact Or.inr ⟨hQ₂' j, hT₂aff _ ((hT₂ _).mpr ⟨j, (hred₂ j).symm⟩)⟩
  have hfltI : ∀ (inst : DecidablePred (ProlongationTuple.IsInftySide P)),
      @Finsupp.filter (Place QQ FF) ℤ _ (ProlongationTuple.IsInftySide P) inst D = 0 :=
    fun inst => (Finsupp.filter_eq_zero_iff _ _).mpr fun V hV => by
      by_contra h; exact (hncusp V h).1 hV
  have hfltZ : ∀ (inst : DecidablePred (ProlongationTuple.IsZeroSide P)),
      @Finsupp.filter (Place QQ FF) ℤ _ (ProlongationTuple.IsZeroSide P) inst D = 0 :=
    fun inst => (Finsupp.filter_eq_zero_iff _ _).mpr fun V hV => by
      by_contra h; exact (hncusp V h).2 hV
  have hr₁' : R.residue₁ ⟨f₁, hf₁₁⟩ ≠ 0 := (residue₁_ne_zero_iff R).mpr hr₁
  have hr₂' : R.residue₂ ⟨f₁, hf₁₂⟩ ≠ 0 := (residue₂_ne_zero_iff R).mpr hr₂
  have hreg₁ : ∀ v : Place k Fb, 0 ≤ v.ord (R.residue₁ ⟨f₁, hf₁₁⟩ : Fb) := by
    intro v
    by_cases hv : φ (φ v) = v
    · by_cases haff : IsAffineGeomPlace k 1 v
      ·
        exact (hRL.1 f₁ hf₁₁ hf₁₂ v hv haff (hnopole₁ v hv)).1 hr₁'
      ·
        obtain ⟨c, hc, hcv⟩ := F_cuspCoverFst P hqN v haff
        have key := hR.2.2.1 f₁ hf₁₁ hf₁₂ hr₁ hr₂ D hDf₁ c hc
        rw [hfltI _, Finsupp.mapDomain_zero, Finsupp.zero_apply, hcv] at key
        omega
    ·
      have key := hR.1 f₁ hf₁₁ hf₁₂ hr₁ hr₂ D hDf₁ v hv
      have h0 : Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) = 0 := hmapFst
      rw [h0, Finsupp.zero_apply] at key
      omega
  have hreg₂ : ∀ v : Place k Fb, 0 ≤ v.ord (R.residue₂ ⟨f₁, hf₁₂⟩ : Fb) := by
    intro v
    by_cases hv : φ (φ v) = v
    · by_cases haff : IsAffineGeomPlace k 1 v
      ·
        have hv' : φ (φ (φ v)) = φ v := by rw [hv]
        have haff' : IsAffineGeomPlace k 1 (φ v) := F_affine_frob v haff
        have := (hRL.1 f₁ hf₁₁ hf₁₂ (φ v) hv' haff' (hnopole₁ (φ v) hv')).2 hr₂'
        rwa [hv] at this
      · obtain ⟨c, hc, hcv⟩ := F_cuspCoverSnd P hqN v haff
        have key := hR.2.2.2 f₁ hf₁₁ hf₁₂ hr₁ hr₂ D hDf₁ c hc
        rw [hfltZ _, Finsupp.mapDomain_zero, Finsupp.zero_apply, hcv] at key
        omega
    · have key := hR.2.1 f₁ hf₁₁ hf₁₂ hr₁ hr₂ D hDf₁ v hv
      have h0 : Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) = 0 := hmapSnd
      rw [h0, Finsupp.zero_apply] at key
      omega
  obtain ⟨κ₁, hκ₁⟩ := F_const (k := k) hqN (R.residue₁ ⟨f₁, hf₁₁⟩ : Fb) hreg₁
  obtain ⟨κ₂, hκ₂⟩ := F_const (k := k) hqN (R.residue₂ ⟨f₁, hf₁₂⟩ : Fb) hreg₂
  have hκ₁0 : κ₁ ≠ 0 := by
    intro h; apply (residue₁_ne_zero_iff R).mpr hr₁; rw [hκ₁, h, map_zero]
  have hκ₂0 : κ₂ ≠ 0 := by
    intro h; apply (residue₂_ne_zero_iff R).mpr hr₂; rw [hκ₂, h, map_zero]

  have hWne : W.Nonempty := by
    by_contra hWe
    rw [Finset.not_nonempty_iff_eq_empty] at hWe
    have := hgp₁ 1 (fun v _ => by rw [Place.ord_one]) (fun v _ => by rw [Place.ord_one]; norm_num)
      (by simp [hWe])
    exact one_ne_zero this
  obtain ⟨w₀, hw₀⟩ := hWne
  have hκ : κ₂ = κ₁ := by

    obtain ⟨hs, hsφ⟩ := F_nodePair (q := q) (data := data) (hKr := hKr) (W := W) w₀ hw₀
    have hfix : φ (φ w₀) = w₀ := F_ss_fixed (data := data) (hKr := hKr) hqN w₀ (hW' w₀ hw₀)
    have havoid : ∀ V : Place QQ FF, V.ord f₁ ≠ 0 →
        ¬ (P.reduceFst V = (w₀, arithFrobC q k 1 • w₀).1 ∧ P.reduceSnd V = (w₀, arithFrobC q k 1 • w₀).2) := by
      rintro V hV ⟨h1, -⟩
      have hD' : D V ≠ 0 := by rwa [hDf₁]
      exact reduceFst_ne_of_fixed hfix (htype V hD') h1
    obtain ⟨cc, -, hcc₁, hcc₂⟩ := hNV f₁ hf₁₁ hf₁₂ hr₁' hr₂' _ hs havoid
    rw [hκ₁] at hcc₁; rw [hκ₂] at hcc₂
    rw [← eq_of_hasValue_algebraMap _ hcc₁, ← eq_of_hasValue_algebraMap _ hcc₂]

  have hdisc : ∀ V : Place QQ FF, P.IsStrictFst V → P.reduceFst V = P.reduceFst Qs → V.ord f₁ = 0 := by
    intro V hV hVv
    rw [← hDf₁]
    by_contra h
    rcases hsupp V h with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hQs' i hVv.symm
    · exact hQs' i (by rw [← hred₁ i]; exact hVv.symm)
    · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ j)
    · exact not_isStrictSnd_of_isStrictFst hV (hQ₂' j)

  have hval : ∃ c₁ : A, Qs.HasValue f₁ (c₁ : QQ) ∧ (P.reduceFst Qs).HasValue (R.residue₁ ⟨f₁, hf₁₁⟩ : Fb) (red c₁) :=
    F_alpha hR hQs f₁ hf₁₁ fun V hV hVv => le_of_eq (hdisc V hV hVv).symm
  obtain ⟨c₁, hc₁Q, hc₁v⟩ := hval
  rw [hκ₁] at hc₁v
  have hredc₁ : red c₁ = κ₁ := eq_of_hasValue_algebraMap _ hc₁v
  have hc₁u : IsUnit c₁ := isUnit_of_red_ne_zero R (by rw [hredc₁]; exact hκ₁0)
  obtain ⟨b, hb⟩ := hc₁u.exists_left_inv
  have hb0 : (b : QQ) ≠ 0 := by
    intro h; have : b = 0 := Subtype.ext h
    rw [this, zero_mul] at hb; exact zero_ne_one hb
  have hredb : red b * κ₁ = 1 := by rw [← hredc₁, ← map_mul, hb, map_one]
  set f₂ : FF := (b : QQ) • f₁ with hf₂_def
  have hf₂₁ : f₂ ∈ R.R₁.integers := smul_mem₁ R hf₁₁ b
  have hf₂₂ : f₂ ∈ R.R₂.integers := smul_mem₂ R hf₁₂ b
  have hres₁f₂ : R.residue₁ ⟨f₂, hf₂₁⟩ = 1 := by
    show R.residue₁ ⟨(b : QQ) • f₁, smul_mem₁ R hf₁₁ b⟩ = 1
    rw [residue₁_smul R b hf₁₁, hκ₁, Algebra.smul_def, ← map_mul, hredb, map_one]
  have hres₂f₂ : R.residue₂ ⟨f₂, hf₂₂⟩ = 1 := by
    show R.residue₂ ⟨(b : QQ) • f₁, smul_mem₂ R hf₁₂ b⟩ = 1
    rw [residue₂_smul R b hf₁₂, hκ₂, hκ, Algebra.smul_def, ← map_mul, hredb, map_one]
  have hf₂val : Qs.HasValue f₂ 1 := by
    have := HasValue.smul Qs hc₁Q (b : QQ)
    rwa [show (b : QQ) * (c₁ : QQ) = 1 from by exact_mod_cast congrArg Subtype.val hb] at this
  have hordf₂ : ∀ V : Place QQ FF, V.ord f₂ = D V := fun V => by rw [hf₂_def, ord_smul V hb0, hDf₁]

  by_cases hg : f₂ - 1 = 0
  · have hf₂1 : f₂ = 1 := sub_eq_zero.mp hg
    have hD0 : D = 0 := by
      ext V; rw [← hordf₂, hf₂1, Place.ord_one, Finsupp.zero_apply]
    have : E - E₀ = 0 := by
      rw [hD_def] at hD0
      rcases smul_eq_zero.mp hD0 with h | h
      · exact absurd (by exact_mod_cast h : n = 0) hn0
      · exact h
    exact sub_eq_zero.mp this
  · exfalso

    have hn0' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    set g : FF := f₂ - 1 with hg_def
    obtain ⟨e₁, he₁m, he₁r⟩ := R.R₁.exists_smul_mem g hg
    obtain ⟨e₂, he₂m, he₂r⟩ := R.R₂.exists_smul_mem g hg
    have he₁0 : e₁ ≠ 0 := R.R₁.smul_const_ne_zero he₁m he₁r
    have he₂0 : e₂ ≠ 0 := R.R₂.smul_const_ne_zero he₂m he₂r
    have hf₂0 : f₂ ≠ 0 := hf₂val.ne_zero one_ne_zero

    have hpf : ∀ V : Place QQ FF, V.ord f₂ ≠ 0 →
        ((∃ i, V = Q₁ i) ∨ (∃ i, V = Q₁' i)) ∨ ((∃ j, V = Q₂ j) ∨ (∃ j, V = Q₂' j)) :=
      fun V hV => hsupp V (by rwa [← hordf₂])
    have hpQ₁ : ∀ i, Q₁' i ≠ Q₁ i → (Q₁ i).ord f₂ = -(n : ℤ) ∧ (Q₁' i).ord f₂ = n := fun i hi => by
      rw [hordf₂, hordf₂, hDQ₁, hDQ₁', if_neg hi, if_neg hi]; exact ⟨rfl, rfl⟩
    have hpQ₁eq : ∀ i, Q₁' i = Q₁ i → (Q₁ i).ord f₂ = 0 := fun i hi => by rw [hordf₂, hDQ₁, if_pos hi]
    have hpQ₂ : ∀ j, Q₂' j ≠ Q₂ j → (Q₂ j).ord f₂ = -(n : ℤ) ∧ (Q₂' j).ord f₂ = n := fun j hj => by
      rw [hordf₂, hordf₂, hDQ₂, hDQ₂', if_neg hj, if_neg hj]; exact ⟨rfl, rfl⟩
    have hpQ₂eq : ∀ j, Q₂' j = Q₂ j → (Q₂ j).ord f₂ = 0 := fun j hj => by rw [hordf₂, hDQ₂, if_pos hj]
    have hordf₂_nonneg : ∀ V : Place QQ FF, (∀ i, V = Q₁ i → Q₁' i = Q₁ i) → (∀ j, V = Q₂ j → Q₂' j = Q₂ j) →
        0 ≤ V.ord f₂ := by
      intro V h1 h2
      by_contra hlt; push Not at hlt
      rcases hpf V hlt.ne with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · rw [hpQ₁eq i (h1 i rfl)] at hlt; exact lt_irrefl _ hlt
      · by_cases hii : Q₁' i = Q₁ i
        · rw [hii, hpQ₁eq i hii] at hlt; exact lt_irrefl _ hlt
        · rw [(hpQ₁ i hii).2] at hlt; exact absurd hlt (not_lt.mpr hn0'.le)
      · rw [hpQ₂eq j (h2 j rfl)] at hlt; exact lt_irrefl _ hlt
      · by_cases hjj : Q₂' j = Q₂ j
        · rw [hjj, hpQ₂eq j hjj] at hlt; exact lt_irrefl _ hlt
        · rw [(hpQ₂ j hjj).2] at hlt; exact absurd hlt (not_lt.mpr hn0'.le)
    have hordg_of_nonneg : ∀ V : Place QQ FF, 0 ≤ V.ord f₂ → 0 ≤ V.ord g := fun V hV =>
      V.ord_nonneg_of_mem (sub_mem (V.mem_of_ord_nonneg hf₂0 hV) (one_mem _))
    have hgpole : ∀ V : Place QQ FF, V.ord g < 0 →
        (∃ i, V = Q₁ i ∧ Q₁' i ≠ Q₁ i) ∨ (∃ j, V = Q₂ j ∧ Q₂' j ≠ Q₂ j) := by
      intro V hV
      by_contra h; push Not at h
      exact absurd (hordg_of_nonneg V (hordf₂_nonneg V h.1 h.2)) (not_le.mpr hV)
    have hgval : Qs.HasValue g 0 := by
      have := HasValue.add Qs hf₂val (Qs.hasValue_algebraMap (-1 : QQ))
      simpa [hg_def, sub_eq_add_neg] using this
    have hres₁f₂' : R.R₁.residue ⟨f₂, hf₂₁⟩ ≠ 0 := (residue₁_ne_zero_iff R).mp (by rw [hres₁f₂]; exact one_ne_zero)
    have hres₂f₂' : R.R₂.residue ⟨f₂, hf₂₂⟩ ≠ 0 := (residue₂_ne_zero_iff R).mp (by rw [hres₂f₂]; exact one_ne_zero)
    have hg0₁ : ∀ i, ∀ V : Place QQ FF, P.IsStrictFst V → P.reduceFst V = P.reduceFst (Q₁ i) → V ≠ Q₁ i →
        V ≠ Q₁' i → V.ord f₂ = 0 := by
      intro i V hV hVv h1 h2
      by_contra h
      rcases hpf V h with (⟨l, rfl⟩ | ⟨l, rfl⟩) | (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · have hli : l = i := hinj₁ (by exact hVv)
        exact h1 (by rw [hli])
      · have hli : l = i := hinj₁ (by show P.reduceFst (Q₁ l) = P.reduceFst (Q₁ i); rw [← hred₁ l]; exact hVv)
        exact h2 (by rw [hli])
      · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ l)
      · exact not_isStrictSnd_of_isStrictFst hV (hQ₂' l)
    have hg0₂ : ∀ j, ∀ V : Place QQ FF, P.IsStrictSnd V → P.reduceSnd V = P.reduceSnd (Q₂ j) → V ≠ Q₂ j →
        V ≠ Q₂' j → V.ord f₂ = 0 := by
      intro j V hV hVv h1 h2
      by_contra h
      rcases hpf V h with (⟨l, rfl⟩ | ⟨l, rfl⟩) | (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · exact not_isStrictSnd_of_isStrictFst (hQ₁ l) hV
      · exact not_isStrictSnd_of_isStrictFst (hQ₁' l) hV
      · have hlj : l = j := hinj₂ (by exact hVv)
        exact h1 (by rw [hlj])
      · have hlj : l = j := hinj₂ (by show P.reduceSnd (Q₂ l) = P.reduceSnd (Q₂ j); rw [← hred₂ l]; exact hVv)
        exact h2 (by rw [hlj])

    have key : ∀ (e : QQ), e ≠ 0 → ∀ (hε₁ : e • g ∈ R.R₁.integers) (hε₂ : e • g ∈ R.R₂.integers),
        (R.R₁.residue ⟨e • g, hε₁⟩ ≠ 0 ∨ R.R₂.residue ⟨e • g, hε₂⟩ ≠ 0) → False := by
      intro e he hε₁ hε₂ hAB
      set ε : FF := e • g with hεg
      have hordε : ∀ V : Place QQ FF, V.ord ε = V.ord g := fun V => by rw [hεg, ord_smul V he]
      have hεpole : ∀ V : Place QQ FF, V.ord ε < 0 →
          (∃ i, V = Q₁ i ∧ Q₁' i ≠ Q₁ i) ∨ (∃ j, V = Q₂ j ∧ Q₂' j ≠ Q₂ j) :=
        fun V hV => hgpole V (by rwa [← hordε])
      have hεstrict : ∀ V : Place QQ FF, V.ord ε < 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := by
        intro V hV
        rcases hεpole V hV with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
        exacts [Or.inl (hQ₁ i), Or.inr (hQ₂ j)]
      have hεT : ∀ V : Place QQ FF, V.ord ε < 0 →
          (P.IsStrictFst V ∧ P.reduceFst V ∈ T₁) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∈ T₂) := by
        intro V hV
        rcases hεpole V hV with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
        · exact Or.inl ⟨hQ₁ i, (hT₁ _).mpr ⟨i, rfl⟩⟩
        · exact Or.inr ⟨hQ₂ j, (hT₂ _).mpr ⟨j, rfl⟩⟩
      have hεval : Qs.HasValue ε 0 := by
        have := HasValue.smul Qs hgval e
        rwa [mul_zero] at this
      set r₁ : Fb := R.residue₁ ⟨ε, hε₁⟩ with hr₁_def
      set r₂ : Fb := R.residue₂ ⟨ε, hε₂⟩ with hr₂_def
      have hr₁_zero_iff : r₁ = 0 ↔ R.R₁.residue ⟨ε, hε₁⟩ = 0 := by
        rw [hr₁_def, R.residue₁_apply]; exact map_eq_zero_iff R.ι R.ι.injective
      have hr₂_zero_iff : r₂ = 0 ↔ R.R₂.residue ⟨ε, hε₂⟩ = 0 := by
        rw [hr₂_def, R.residue₂_apply]; exact map_eq_zero_iff R.ι R.ι.injective

      have hεfix : ∀ v : Place k Fb, φ (φ v) = v → ∀ V : Place QQ FF, P.reduceFst V = v → 0 ≤ V.ord ε := by
        intro v hv V hVv
        by_contra hlt; push Not at hlt
        exact reduceFst_ne_of_fixed hv (hεstrict V hlt) hVv
      have hεcusp : ∀ V : Place QQ FF, V.ord ε < 0 →
          ¬ ProlongationTuple.IsInftySide P V ∧ ¬ ProlongationTuple.IsZeroSide P V := by
        intro V hV
        refine (fun h => not_side_of_affine P V h.1 h.2) (affine_both_of_strict P V ?_)
        rcases hεT V hV with ⟨hs, h⟩ | ⟨hs, h⟩
        exacts [Or.inl ⟨hs, hT₁aff _ h⟩, Or.inr ⟨hs, hT₂aff _ h⟩]

      have hr₁v : (P.reduceFst Qs).HasValue r₁ 0 := by
        obtain ⟨c, hcQ, hcv⟩ := F_alpha hR hQs ε hε₁ (fun V hV hVv => by
          by_contra hlt; push Not at hlt
          rcases hεpole V hlt with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
          · exact hQs' i hVv.symm
          · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ j))
        have hc0 : c = 0 := by
          have h : ((c : QQ)) = 0 := hcQ.unique hεval
          exact_mod_cast h
        rw [hc0, map_zero] at hcv
        exact hcv

      have hnode : ∀ w ∈ W, ∃ c : k, w.HasValue r₁ c ∧ (φ w).HasValue r₂ c := by
        intro w hw
        obtain ⟨hs, hsφ⟩ := F_nodePair (q := q) (data := data) (hKr := hKr) (W := W) w hw
        have hfix : φ (φ w) = w := F_ss_fixed (data := data) (hKr := hKr) hqN w (hW' w hw)
        obtain ⟨c, hc₁, hc₂⟩ := hRL.2 ε hε₁ hε₂ _ hs (hεfix w hfix)
        refine ⟨c, hc₁, ?_⟩
        rw [← hsφ]; exact hc₂

      have hunit : ∀ μ : A, red μ ≠ 0 → (∀ κ : k, r₂ = cstb κ → red μ + κ ≠ 0) →
          ∃ (hu₁ : cst (μ : QQ) + ε ∈ R.R₁.integers) (hu₂ : cst (μ : QQ) + ε ∈ R.R₂.integers),
            R.R₁.residue ⟨_, hu₁⟩ ≠ 0 ∧ R.R₂.residue ⟨_, hu₂⟩ ≠ 0 ∧
            R.residue₁ ⟨_, hu₁⟩ = cstb (red μ) + r₁ ∧ R.residue₂ ⟨_, hu₂⟩ = cstb (red μ) + r₂ ∧
            (∀ V : Place QQ FF, 0 ≤ V.ord ε → 0 ≤ V.ord (cst (μ : QQ) + ε)) ∧
            ∃ D : Divisor QQ FF, ∀ W, D W = W.ord (cst (μ : QQ) + ε) := by
        intro μ hμ0 hμκ
        have hu₁ : cst (μ : QQ) + ε ∈ R.R₁.integers := add_mem (cst_mem₁ R μ) hε₁
        have hu₂ : cst (μ : QQ) + ε ∈ R.R₂.integers := add_mem (cst_mem₂ R μ) hε₂
        have hres₁ : R.residue₁ ⟨_, hu₁⟩ = cstb (red μ) + r₁ := by
          have : (⟨_, hu₁⟩ : R.R₁.integers) = ⟨cst (μ : QQ), cst_mem₁ R μ⟩ + ⟨ε, hε₁⟩ := Subtype.ext rfl
          rw [this, map_add, residue₁_cst R]
        have hres₂ : R.residue₂ ⟨_, hu₂⟩ = cstb (red μ) + r₂ := by
          have : (⟨_, hu₂⟩ : R.R₂.integers) = ⟨cst (μ : QQ), cst_mem₂ R μ⟩ + ⟨ε, hε₂⟩ := Subtype.ext rfl
          rw [this, map_add, residue₂_cst R]
        have hordu : ∀ V : Place QQ FF, 0 ≤ V.ord ε → 0 ≤ V.ord (cst (μ : QQ) + ε) := fun V hV =>
          V.ord_nonneg_of_mem (add_mem (V.algebraMap_mem' _) (mem_of_ord_nonneg' V hV))
        refine ⟨hu₁, hu₂, ?_, ?_, hres₁, hres₂, hordu, ?_⟩
        · rw [← residue₁_ne_zero_iff R, hres₁]
          have hval : (P.reduceFst Qs).HasValue (cstb (red μ) + r₁) (red μ + 0) :=
            HasValue.add _ ((P.reduceFst Qs).hasValue_algebraMap _) hr₁v
          rw [add_zero] at hval
          exact hval.ne_zero hμ0
        · rw [← residue₂_ne_zero_iff R, hres₂]
          intro h
          have : r₂ = cstb (-red μ) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_right h
          exact hμκ (-red μ) this (by simp)
        · have hu0 : cst (μ : QQ) + ε ≠ 0 := by
            have hval : Qs.HasValue (cst (μ : QQ) + ε) ((μ : QQ) + 0) :=
              HasValue.add Qs (Qs.hasValue_algebraMap _) hεval
            rw [add_zero] at hval
            refine hval.ne_zero ?_
            intro h; apply hμ0
            have : μ = 0 := Subtype.ext h
            rw [this, map_zero]
          exact exists_divisor (1 * q) _ hu0

      have hreg_of_unit : ∀ (μ : A) (hu₁ : cst (μ : QQ) + ε ∈ R.R₁.integers) (hu₂ : cst (μ : QQ) + ε ∈ R.R₂.integers),
          R.R₁.residue ⟨_, hu₁⟩ ≠ 0 → R.R₂.residue ⟨_, hu₂⟩ ≠ 0 →
          R.residue₁ ⟨_, hu₁⟩ = cstb (red μ) + r₁ → R.residue₂ ⟨_, hu₂⟩ = cstb (red μ) + r₂ →
          (∀ V : Place QQ FF, 0 ≤ V.ord ε → 0 ≤ V.ord (cst (μ : QQ) + ε)) →
          ∀ D : Divisor QQ FF, (∀ W, D W = W.ord (cst (μ : QQ) + ε)) →
          (∀ v : Place k Fb, (∀ V : Place QQ FF, P.IsStrictFst V → P.reduceFst V = v → 0 ≤ V.ord ε) →
              0 ≤ v.ord r₁) ∧
          (∀ v : Place k Fb, (∀ V : Place QQ FF, P.IsStrictSnd V → P.reduceSnd V = v → 0 ≤ V.ord ε) →
              0 ≤ v.ord r₂) := by
        intro μ hu₁ hu₂ hur₁ hur₂ hres₁ hres₂ hordu D hD
        have hur₁' : R.residue₁ ⟨_, hu₁⟩ ≠ 0 := (residue₁_ne_zero_iff R).mpr hur₁
        have hur₂' : R.residue₂ ⟨_, hu₂⟩ ≠ 0 := (residue₂_ne_zero_iff R).mpr hur₂
        have hDnn : ∀ V : Place QQ FF, 0 ≤ V.ord ε → 0 ≤ D V := fun V hV => by rw [hD]; exact hordu V hV
        have hufix : ∀ v : Place k Fb, φ (φ v) = v → ∀ V : Place QQ FF, P.reduceFst V = v →
            0 ≤ V.ord (cst (μ : QQ) + ε) := fun v hv V hVv => hordu V (hεfix v hv V hVv)
        constructor
        · intro v hvdisc
          refine ord_nonneg_of_ord_add_algebraMap_nonneg v (red μ) ?_
          rw [← hres₁]
          by_cases hv : φ (φ v) = v
          · by_cases haff : IsAffineGeomPlace k 1 v
            · exact (hRL.1 _ hu₁ hu₂ v hv haff (hufix v hv)).1 hur₁'
            · obtain ⟨c, hc, hcv⟩ := F_cuspCoverFst P hqN v haff
              rw [← hcv, ← hR.2.2.1 _ hu₁ hu₂ hur₁ hur₂ D hD c hc]
              refine mapDomain_apply_nonneg _ _ _ fun V _ => ?_
              rw [Finsupp.filter_apply]
              split_ifs with hI
              · refine hDnn V ?_
                by_contra hlt; push Not at hlt
                exact (hεcusp V hlt).1 hI
              · exact le_rfl
          · rw [← hR.1 _ hu₁ hu₂ hur₁ hur₂ D hD v hv]
            refine mapDomain_apply_nonneg _ _ _ fun V hVv => ?_
            rw [Finsupp.filter_apply]
            split_ifs with hI
            · exact hDnn V (hvdisc V hI hVv)
            · exact le_rfl
        · intro v hvdisc
          refine ord_nonneg_of_ord_add_algebraMap_nonneg v (red μ) ?_
          rw [← hres₂]
          by_cases hv : φ (φ v) = v
          · by_cases haff : IsAffineGeomPlace k 1 v
            · have hv' : φ (φ (φ v)) = φ v := by rw [hv]
              have haff' : IsAffineGeomPlace k 1 (φ v) := F_affine_frob v haff
              have := (hRL.1 _ hu₁ hu₂ (φ v) hv' haff' (hufix (φ v) hv')).2 hur₂'
              rwa [hv] at this
            · obtain ⟨c, hc, hcv⟩ := F_cuspCoverSnd P hqN v haff
              rw [← hcv, ← hR.2.2.2 _ hu₁ hu₂ hur₁ hur₂ D hD c hc]
              refine mapDomain_apply_nonneg _ _ _ fun V _ => ?_
              rw [Finsupp.filter_apply]
              split_ifs with hI
              · refine hDnn V ?_
                by_contra hlt; push Not at hlt
                exact (hεcusp V hlt).2 hI
              · exact le_rfl
          · rw [← hR.2.1 _ hu₁ hu₂ hur₁ hur₂ D hD v hv]
            refine mapDomain_apply_nonneg _ _ _ fun V hVv => ?_
            rw [Finsupp.filter_apply]
            split_ifs with hI
            · exact hDnn V (hvdisc V hI hVv)
            · exact le_rfl

      have hoffT₁ : ∀ v : Place k Fb, v ∉ T₁ →
          ∀ V : Place QQ FF, P.IsStrictFst V → P.reduceFst V = v → 0 ≤ V.ord ε := by
        intro v hv V hI hVv
        by_contra hlt; push Not at hlt
        rcases hεT V hlt with ⟨-, hT⟩ | ⟨hS, -⟩
        · exact hv (hVv ▸ hT)
        · exact not_isStrictSnd_of_isStrictFst hI hS
      have hoffT₂ : ∀ v : Place k Fb, v ∉ T₂ →
          ∀ V : Place QQ FF, P.IsStrictSnd V → P.reduceSnd V = v → 0 ≤ V.ord ε := by
        intro v hv V hI hVv
        by_contra hlt; push Not at hlt
        rcases hεT V hlt with ⟨hF, -⟩ | ⟨-, hT⟩
        · exact not_isStrictSnd_of_isStrictFst hF hI
        · exact hv (hVv ▸ hT)

      have hε0 : ε ≠ 0 := fun h => by
        rcases hAB with hA | hB
        · apply hA
          have : (⟨ε, hε₁⟩ : R.R₁.integers) = 0 := Subtype.ext h
          rw [this, map_zero]
        · apply hB
          have : (⟨ε, hε₂⟩ : R.R₂.integers) = 0 := Subtype.ext h
          rw [this, map_zero]
      have hcst : cst e⁻¹ = g * ε⁻¹ := by
        rw [hεg, Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm g, mul_assoc, mul_inv_cancel₀ (by
          intro h0; apply hε0; rw [hεg, Algebra.smul_def, h0, mul_zero]), mul_one, map_inv₀]
      have heA : e⁻¹ ∈ A := by
        rcases hAB with hA | hB
        · have hεinv : ε⁻¹ ∈ R.R₁.integers := inv_mem_of_isUnit hε₁ (R.R₁.isUnit_of_residue_ne_zero hA)
          exact (R.R₁.algebraMap_mem_iff _).mp (hcst ▸ mul_mem (sub_mem hf₂₁ (one_mem _)) hεinv)
        · have hεinv : ε⁻¹ ∈ R.R₂.integers := inv_mem_of_isUnit hε₂ (R.R₂.isUnit_of_residue_ne_zero hB)
          exact (R.R₂.algebraMap_mem_iff _).mp (hcst ▸ mul_mem (sub_mem hf₂₂ (one_mem _)) hεinv)
      have hgε : f₂ = 1 + cst ((⟨e⁻¹, heA⟩ : A) : QQ) * ε := by
        show f₂ = 1 + cst e⁻¹ * ε
        rw [hεg, hg_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one]
        ring

      have hsimple₁ : R.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
          (∀ v : Place k Fb, (∀ V : Place QQ FF, P.IsStrictFst V → P.reduceFst V = v → 0 ≤ V.ord ε) → 0 ≤ v.ord r₁) →
          ∀ v ∈ T₁, -1 ≤ v.ord r₁ := by
        intro hA hreg v hv
        obtain ⟨i, rfl⟩ := (hT₁ v).mp hv
        by_cases hii : Q₁' i = Q₁ i
        ·
          have h0 : 0 ≤ (P.reduceFst (Q₁ i)).ord r₁ := by
            refine hreg _ fun V hV hVv => ?_
            by_contra hlt; push Not at hlt
            rcases hεpole V hlt with ⟨l, rfl, hl⟩ | ⟨j, rfl, -⟩
            · have hli : l = i := hinj₁ (by exact hVv)
              subst hli; exact hl hii
            · exact not_isStrictSnd_of_isStrictFst hV (hQ₂ j)
          omega
        · exact F_LFst hR (hQ₁ i) (hQ₁' i) (hred₁ i) hii (hT₁aff _ hv) hqN _ rfl (hQ₁j i).1 (hQ₁j i).2 n hn f₂ hf₂₁
            hres₁f₂' (hpQ₁ i hii).1 (hpQ₁ i hii).2 (hg0₁ i) ⟨e⁻¹, heA⟩ ε hε₁ hA hgε
      have hsimple₂ : R.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
          (∀ v : Place k Fb, (∀ V : Place QQ FF, P.IsStrictSnd V → P.reduceSnd V = v → 0 ≤ V.ord ε) → 0 ≤ v.ord r₂) →
          ∀ v ∈ T₂, -1 ≤ v.ord r₂ := by
        intro hB hreg v hv
        obtain ⟨j, rfl⟩ := (hT₂ v).mp hv
        by_cases hjj : Q₂' j = Q₂ j
        · have h0 : 0 ≤ (P.reduceSnd (Q₂ j)).ord r₂ := by
            refine hreg _ fun V hV hVv => ?_
            by_contra hlt; push Not at hlt
            rcases hεpole V hlt with ⟨i, rfl, -⟩ | ⟨l, rfl, hl⟩
            · exact not_isStrictSnd_of_isStrictFst (hQ₁ i) hV
            · have hlj : l = j := hinj₂ (by exact hVv)
              subst hlj; exact hl hjj
          omega
        · exact F_LSnd hR (hQ₂ j) (hQ₂' j) (hred₂ j) hjj (hT₂aff _ hv) hqN _ rfl (hQ₂j j).1 (hQ₂j j).2 n hn f₂ hf₂₂
            hres₂f₂' (hpQ₂ j hjj).1 (hpQ₂ j hjj).2 (hg0₂ j) ⟨e⁻¹, heA⟩ ε hε₂ hB hgε

      have hr₂const : ∃ κ : k, r₂ = cstb κ := by
        by_cases hB : R.R₂.residue ⟨ε, hε₂⟩ = 0
        · exact ⟨0, by rw [map_zero]; exact hr₂_zero_iff.mpr hB⟩
        · by_contra hnc
          push Not at hnc
          obtain ⟨hu₁, hu₂, hur₁, hur₂, hres₁, hres₂, hordu, D, hD⟩ :=
            hunit 1 (by rw [map_one]; exact one_ne_zero) (fun κ hκ _ => (hnc κ hκ).elim)
          obtain ⟨-, hreg₂⟩ := hreg_of_unit 1 hu₁ hu₂ hur₁ hur₂ hres₁ hres₂ hordu D hD
          obtain ⟨κ, hκ⟩ := hgp₂ r₂ (fun v hv => hreg₂ v (hoffT₂ v hv)) (hsimple₂ hB hreg₂)
          exact hnc κ hκ
      obtain ⟨κ', hκ'⟩ := hr₂const

      have hvalW : ∀ w ∈ W, w.HasValue r₁ κ' := by
        intro w hw
        obtain ⟨c, hc₁, hc₂⟩ := hnode w hw
        rw [hκ'] at hc₂
        rwa [eq_of_hasValue_algebraMap _ hc₂] at hc₁

      obtain ⟨μ, hμ0, hμκ⟩ := exists_mu (A := A) (red := red) (-κ')
      obtain ⟨hu₁, hu₂, hur₁, hur₂, hres₁, hres₂, hordu, D, hD⟩ := hunit μ hμ0 (fun κ hκ h => by
        have hκκ : κ = κ' := (algebraMap k Fb).injective (hκ.symm.trans hκ')
        apply hμκ; rw [← hκκ]; exact eq_neg_of_add_eq_zero_left h)
      obtain ⟨hreg₁, -⟩ := hreg_of_unit μ hu₁ hu₂ hur₁ hur₂ hres₁ hres₂ hordu D hD
      by_cases hA : R.R₁.residue ⟨ε, hε₁⟩ = 0
      ·
        have hr₁0 : r₁ = 0 := hr₁_zero_iff.mpr hA
        have hB : R.R₂.residue ⟨ε, hε₂⟩ ≠ 0 := by
          rcases hAB with h | h
          exacts [absurd hA h, h]
        have hκ0 : κ' = 0 := by
          have h := hvalW w₀ hw₀
          rw [hr₁0] at h
          exact h.unique (hasValue_zero _)
        apply hB
        rw [← hr₂_zero_iff, hκ', hκ0, map_zero]
      ·

        have h1 : r₁ = cstb κ' := by
          by_cases h10 : r₁ - cstb κ' = 0
          · exact sub_eq_zero.mp h10
          · exfalso; apply h10
            refine hgp₁ (r₁ - cstb κ') (fun v hv => ?_) (fun v hv => ?_) (fun w hw => ?_)
            · exact v.ord_nonneg_of_mem (sub_mem (mem_of_ord_nonneg' v (hreg₁ v (hoffT₁ v hv))) (v.algebraMap_mem' _))
            · exact le_ord_sub_algebraMap v κ' (by norm_num) (hsimple₁ hA hreg₁ v hv) h10
            · have := HasValue.add w (hvalW w hw) (w.hasValue_algebraMap (-κ'))
              rw [add_neg_cancel, map_neg, ← sub_eq_add_neg] at this
              exact this
        rw [h1] at hr₁v
        have hκ0 : κ' = 0 := (eq_of_hasValue_algebraMap _ hr₁v).symm
        apply hA
        rw [← hr₁_zero_iff, h1, hκ0, map_zero]

    rcases A.mem_or_inv_mem (e₁ / e₂) with h | h
    · have hε₂ : e₁ • g ∈ R.R₂.integers := by
        have : e₁ • g = ((⟨e₁ / e₂, h⟩ : A) : QQ) • (e₂ • g) := by
          rw [smul_smul]; congr 1; field_simp
        rw [this]; exact smul_mem₂ R he₂m _
      exact key e₁ he₁0 he₁m hε₂ (Or.inl he₁r)
    · have h' : e₂ / e₁ ∈ A := by rwa [inv_div] at h
      have hε₁ : e₂ • g ∈ R.R₁.integers := by
        have : e₂ • g = ((⟨e₂ / e₁, h'⟩ : A) : QQ) • (e₁ • g) := by
          rw [smul_smul]; congr 1; field_simp
        rw [this]; exact smul_mem₁ R he₁m _
      exact key e₂ he₂0 hε₁ he₂m (Or.inr he₂r)

end Main

end Ws28.CoreOne

end

p2m_open "ModularCurve~isCurveOver_modularFunctionFieldBar~nodePairsOf" in p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~LevelOneProlongationPair~IsCuspidal~IsZeroSide~IsCuspidal'~IsStrictTypeOne~redSnd~redFst" in open AlgebraicCurve  in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hNV : R.NodeValueLaw W) (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hQ₁j : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 1728)
    (hQ₂j : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 1728)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (n : ℕ) (hn : (n : k) ≠ 0) (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      V.ord f = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :=
  Ws28.CoreOne.core hR hW hNV hRL Q₁ Q₁' Q₂ Q₂' hQ₁ hQ₁' hQ₂ hQ₂' hinj₁ hinj₂ hred₁ hred₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff
    hQ₁j hQ₂j hgp₁ hgp₂ Qs hQs hQs' n hn f hf hdiv

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne (solution)
