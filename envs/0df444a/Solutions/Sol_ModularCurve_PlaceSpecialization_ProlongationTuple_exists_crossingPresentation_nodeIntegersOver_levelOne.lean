-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7fba27cc-3475-5bb3-94b1-c916c7d678e3

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
import Theorems.Thm_ModularCurve_NodeLocalized_modularRedLocHom_frickeInvolutionBar_eq_zero_iff_mem_span_branchSnd
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_NodeLocalized_ord_modularRedLocHom_eq_iff_exists_isUnit
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk"
p2m_attr_erase "simp" "AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace D4A1
namespace Transport

variable {S T : Type*} [CommRing S] [CommRing T]

theorem map_span_singleton (e : S ≃+* T) (s : S) :
    Ideal.map (e : S →+* T) (Ideal.span {s}) = Ideal.span {e s} := by
  rw [Ideal.map_span, Set.image_singleton]; rfl

theorem map_span_pair (e : S ≃+* T) (s₁ s₂ : S) :
    Ideal.map (e : S →+* T) (Ideal.span {s₁, s₂}) = Ideal.span {e s₁, e s₂} := by
  rw [Ideal.map_span, Set.image_pair]; rfl

theorem map_span_triple (e : S ≃+* T) (s₁ s₂ s₃ : S) :
    Ideal.map (e : S →+* T) (Ideal.span {s₁, s₂, s₃}) = Ideal.span {e s₁, e s₂, e s₃} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_pair]; rfl

theorem map_symm_span_pair (e : S ≃+* T) (t₁ t₂ : T) :
    Ideal.map (e.symm : T →+* S) (Ideal.span {t₁, t₂}) = Ideal.span {e.symm t₁, e.symm t₂} :=
  map_span_pair e.symm t₁ t₂

theorem map_symm_span_triple (e : S ≃+* T) (t₁ t₂ t₃ : T) :
    Ideal.map (e.symm : T →+* S) (Ideal.span {t₁, t₂, t₃}) = Ideal.span {e.symm t₁, e.symm t₂, e.symm t₃} :=
  map_span_triple e.symm t₁ t₂ t₃

theorem comap_eq_map_symm (e : S ≃+* T) (J : Ideal T) :
    Ideal.comap (e : S →+* T) J = Ideal.map (e.symm : T →+* S) J :=
  (Ideal.map_symm (f := e)).symm

theorem map_eq_comap_symm (e : S ≃+* T) (I : Ideal S) :
    Ideal.map (e : S →+* T) I = Ideal.comap (e.symm : T →+* S) I :=
  Ideal.map_comap_of_equiv (e : S ≃+* T)

theorem mem_map_iff (e : S ≃+* T) (I : Ideal S) (t : T) :
    t ∈ Ideal.map (e : S →+* T) I ↔ e.symm t ∈ I := by
  rw [map_eq_comap_symm, Ideal.mem_comap]; rfl

theorem apply_mem_map_iff (e : S ≃+* T) (I : Ideal S) (s : S) :
    e s ∈ Ideal.map (e : S →+* T) I ↔ s ∈ I := by
  rw [mem_map_iff, RingEquiv.symm_apply_apply]

theorem apply_not_mem_map_iff (e : S ≃+* T) (I : Ideal S) (s : S) :
    e s ∉ Ideal.map (e : S →+* T) I ↔ s ∉ I :=
  (apply_mem_map_iff e I s).not

theorem isPrime_map_iff (e : S ≃+* T) (I : Ideal S) :
    (Ideal.map (e : S →+* T) I).IsPrime ↔ I.IsPrime := by
  constructor
  · intro h
    have := Ideal.comap_isPrime (e : S →+* T) (Ideal.map (e : S →+* T) I)
    rwa [Ideal.comap_map_of_bijective (e : S →+* T) e.bijective] at this
  · intro h
    exact Ideal.map_isPrime_of_equiv e

theorem isMaximal_map_iff (e : S ≃+* T) (I : Ideal S) :
    (Ideal.map (e : S →+* T) I).IsMaximal ↔ I.IsMaximal := by
  constructor
  · intro h
    haveI := h
    have h' : (Ideal.comap (e : S →+* T) (Ideal.map (e : S →+* T) I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (e : S →+* T) e.surjective
    rwa [Ideal.comap_map_of_bijective (e : S →+* T) e.bijective] at h'
  · intro h
    exact Ideal.map_isMaximal_of_equiv e

theorem eq_map_symm_maximalIdeal_of_isMaximal [IsLocalRing T] (e : S ≃+* T) (M : Ideal S) (hM : M.IsMaximal) :
    M = Ideal.map (e.symm : T →+* S) (IsLocalRing.maximalIdeal T) := by
  have h1 : (Ideal.map (e : S →+* T) M).IsMaximal := (isMaximal_map_iff e M).mpr hM
  have h2 : Ideal.map (e : S →+* T) M = IsLocalRing.maximalIdeal T := IsLocalRing.eq_maximalIdeal h1
  rw [← h2, ← comap_eq_map_symm, Ideal.comap_map_of_bijective (e : S →+* T) e.bijective]

theorem eq_map_symm_of_isMaximal_of_maximalIdeal_eq [IsLocalRing T] (e : S ≃+* T) {I : Ideal T}
    (hI : IsLocalRing.maximalIdeal T = I) (M : Ideal S) (hM : M.IsMaximal) :
    M = Ideal.map (e.symm : T →+* S) I := by
  rw [← hI]; exact eq_map_symm_maximalIdeal_of_isMaximal e M hM

theorem isMaximal_map_symm_maximalIdeal [IsLocalRing T] (e : S ≃+* T) :
    (Ideal.map (e.symm : T →+* S) (IsLocalRing.maximalIdeal T)).IsMaximal :=
  (isMaximal_map_iff e.symm _).mpr (IsLocalRing.maximalIdeal.isMaximal T)

theorem isUnit_symm_iff (e : S ≃+* T) (t : T) : IsUnit (e.symm t) ↔ IsUnit t :=
  ⟨fun h => by simpa using h.map e, fun h => h.map e.symm⟩

end D4A1.Transport

namespace D4A1
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ
section Iso

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P₁ : PlaceSpecialization A q 1 data hKr k red hα₁ hβ₁}

noncomputable def qExpHom (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a) :
    ↥(R.nodeIntegersOver K w) →+*
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) where
  toFun g := (⟨((g : ↥(modularFunctionFieldBar (1 * q))) : LQ),
    (mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver R hmodel W hW hreg K w hw a ha x hx _).mpr
      ⟨g, g.2, rfl⟩⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
  map_one' := Subtype.ext (by simp)
  map_mul' f g := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

theorem qExpHom_bijective (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a) :
    Function.Bijective (qExpHom R hmodel W hW hreg K w hw a ha x hx) := by
  constructor
  · intro f g h
    have h' : (((f : ↥(modularFunctionFieldBar (1 * q))) : LQ)) = ((g : ↥(modularFunctionFieldBar (1 * q))) : LQ) :=
      congrArg (fun z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) => (z : LQ)) h
    exact Subtype.ext (Subtype.ext h')
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg, hgf⟩ :=
      (mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver R hmodel W hW hreg K w hw a ha x hx f).mp hf
    exact ⟨⟨g, hg⟩, Subtype.ext hgf⟩

noncomputable def qExpIso (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a) :
    ↥(R.nodeIntegersOver K w) ≃+*
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
  RingEquiv.ofBijective (qExpHom R hmodel W hW hreg K w hw a ha x hx) (qExpHom_bijective R hmodel W hW hreg K w hw a ha x hx)

variable (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)

@[scoped simp] theorem coe_qExpIso (g : ↥(R.nodeIntegersOver K w)) :
    ((qExpIso R hmodel W hW hreg K w hw a ha x hx g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K)
      (redRestrict red K) a (a ^ q))) : LQ) = ((g : ↥(modularFunctionFieldBar (1 * q))) : LQ) := rfl

theorem coe_coe_qExpIso_symm
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ((((qExpIso R hmodel W hW hreg K w hw a ha x hx).symm f : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (1 * q))) : LQ) = (f : LQ) := by
  conv_rhs => rw [← (qExpIso R hmodel W hW hreg K w hw a ha x hx).apply_symm_apply f]
  rfl

theorem qExpIso_nodeConst (c : ↥(coeffSubring A K)) :
    qExpIso R hmodel W hW hreg K w hw a ha x hx (R.nodeConst K w c) =
      ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ := by
  apply Subtype.ext
  rw [coe_qExpIso, coe_nodeConst]
  simp [modularEval, CharPReduction.constSeries]

end Iso

section Residues

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P₁ : PlaceSpecialization A q 1 data hKr k red hα₁ hβ₁}

theorem ha2_of (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') : a ^ (q ^ 2) = a := by
  have hss : w.evalAt (jGeomGen k 1) ∈ ssJSet q k := ((isSupersingularPlace_iff q 1 k w).mp (hW w hw)).2.2
  rw [ha] at hss
  exact pow_q_sq_eq_self_of_mem_ssJSet q hss

theorem nodeResidue₁_eq_zero_iff (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') (g : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ↔
      qExpIso R hmodel W hW hreg K w hw a ha x hx g ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
  have hgF1 : (g : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers := g.2.1.1
  have hloc : (((g : ↥(modularFunctionFieldBar (1 * q))) : LQ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := (R.mem_integersFst_iff _).mp hgF1
  obtain ⟨h, hres⟩ := R.residue₁_eq_modularRedLocHom (g : ↥(modularFunctionFieldBar (1 * q))) hloc
  have key : R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ↔
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hloc⟩ = 0 := by
    rw [nodeResidue₁_apply, residue₁_apply]
    change R.ι (R.R₁.residue ⟨(g : ↥(modularFunctionFieldBar (1 * q))), h⟩) = 0 ↔ _
    rw [← hres]
    constructor
    · intro h0; rw [h0]; rfl
    · intro h0; exact Subtype.ext h0

  have hmemR₀ := (mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver R hmodel W hW hreg K w hw a ha x hx
    (((g : ↥(modularFunctionFieldBar (1 * q))) : LQ))).mpr ⟨g, g.2, rfl⟩
  have hrw : qExpIso R hmodel W hW hreg K w hw a ha x hx g = ⟨_, hmemR₀⟩ := Subtype.ext (coe_qExpIso R hmodel W hW hreg K w hw a ha x hx g)
  rw [key, hrw]
  exact modularRedLocHom_eq_zero_iff_mem_span_branchFst red a (ha2_of R hmodel W hW hreg K w hw a ha x hx ϖ hϖ) K ϖ hϖ ⟨_, hmemR₀⟩ hloc

theorem atkinLehnerBar_one_eq (q : ℕ) [Fact q.Prime] :
    atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) :=
  geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q

theorem nodeResidue₂_eq_zero_iff (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') (g : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ↔
      qExpIso R hmodel W hW hreg K w hw a ha x hx g ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
  have hgF2 : (g : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₂.integers := g.2.1.2.1
  have hloc2 : ((atkinLehnerBar 1 q (g : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LQ) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := (R.mem_integersSnd_iff _).mp hgF2
  obtain ⟨h, hres⟩ := R.residue₁_eq_modularRedLocHom _ hloc2
  have key : R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ↔
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hloc2⟩ = 0 := by
    rw [nodeResidue₂_apply, residue₂_apply, R.residue₂_eq]
    change R.ι (R.R₁.residue ⟨atkinLehnerBar 1 q (g : ↥(modularFunctionFieldBar (1 * q))), h⟩) = 0 ↔ _
    rw [← hres]
    constructor
    · intro h0; rw [h0]; rfl
    · intro h0; exact Subtype.ext h0

  have hmemR₀ := (mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver R hmodel W hW hreg K w hw a ha x hx
    (((g : ↥(modularFunctionFieldBar (1 * q))) : LQ))).mpr ⟨g, g.2, rfl⟩
  have hrw : qExpIso R hmodel W hW hreg K w hw a ha x hx g = ⟨_, hmemR₀⟩ := Subtype.ext (coe_qExpIso R hmodel W hW hreg K w hw a ha x hx g)
  have hgF : (((g : ↥(modularFunctionFieldBar (1 * q))) : LQ)) ∈ modularFunctionFieldBar (1 * q) :=
    (g : ↥(modularFunctionFieldBar (1 * q))).2
  have heq : (⟨(((g : ↥(modularFunctionFieldBar (1 * q))) : LQ)), hgF⟩ : ↥(modularFunctionFieldBar (1 * q))) =
      (g : ↥(modularFunctionFieldBar (1 * q))) := Subtype.ext rfl
  have hALg : atkinLehnerBar 1 q (g : ↥(modularFunctionFieldBar (1 * q))) =
      frickeInvolutionBar (1 * q) ⟨(((g : ↥(modularFunctionFieldBar (1 * q))) : LQ)), hgF⟩ := by
    rw [atkinLehnerBar_one_eq, heq]
  have hloc2' : ((frickeInvolutionBar (1 * q) ⟨(((g : ↥(modularFunctionFieldBar (1 * q))) : LQ)), hgF⟩ :
      ↥(modularFunctionFieldBar (1 * q))) : LQ) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [← hALg]; exact hloc2
  have hsub : (⟨_, hloc2⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hloc2'⟩ := by
    apply Subtype.ext
    show ((atkinLehnerBar 1 q (g : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LQ) = _
    rw [hALg]
  rw [key, hsub, hrw]
  exact modularRedLocHom_frickeInvolutionBar_eq_zero_iff_mem_span_branchSnd red a (ha2_of R hmodel W hW hreg K w hw a ha x hx ϖ hϖ) K ϖ hϖ ⟨_, hmemR₀⟩ hgF hloc2'

theorem ord_nodeResidue_nonneg (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') (g : ↥(R.nodeIntegersOver K w)) :
    (R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 → 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
    (R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 → 0 ≤ (arithFrobC q k 1 • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hw' := hW w hw
  have hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w := by
    rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w,
      ← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr]
    exact arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hq1 k w hw'
  have h := hreg.1 (g : ↥(modularFunctionFieldBar (1 * q))) g.2.1.1 g.2.1.2.1 w hfix
    ((isSupersingularPlace_iff q 1 k w).mp hw').2.1 (fun V hV => ord_nonneg_of_mem_nodeIntegers R g.2.1 hV)
  rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w] at h
  exact h

end Residues

section Assembly

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P₁ : PlaceSpecialization A q 1 data hKr k red hα₁ hβ₁}

noncomputable def res₂S (R : ProlongationTuple P₁) [IsAlgClosed k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k 1)) : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k 1) :=
  (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

noncomputable def res₁S (R : ProlongationTuple P₁) [IsAlgClosed k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k 1)) : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k 1) :=
  (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

theorem res₂S_apply (R : ProlongationTuple P₁) [IsAlgClosed k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k 1)) (g : ↥(R.nodeIntegersOver K w)) :
    res₂S R K w g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := rfl

theorem res₁S_apply (R : ProlongationTuple P₁) [IsAlgClosed k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k 1)) (g : ↥(R.nodeIntegersOver K w)) :
    res₁S R K w g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := rfl

theorem ord_eq_of_mutual {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {r r₀ b b' : F} (hr : r = b * r₀) (hr₀ : r₀ = b' * r) (h0 : r₀ ≠ 0)
    (hb : b ≠ 0 → 0 ≤ v.ord b) (hb' : b' ≠ 0 → 0 ≤ v.ord b') : v.ord r = v.ord r₀ := by
  have h1 : b' * b = 1 := by
    have h2 : (b' * b) * r₀ = 1 * r₀ := by rw [one_mul, mul_assoc, ← hr, ← hr₀]
    exact mul_right_cancel₀ h0 h2
  have hbne : b ≠ 0 := fun h => by rw [h, mul_zero] at h1; exact zero_ne_one h1
  have hb'ne : b' ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  have hsum : v.ord b' + v.ord b = 0 := by rw [← v.ord_mul hb'ne hbne, h1, v.ord_one]
  have hb0 : v.ord b = 0 := by have := hb hbne; have := hb' hb'ne; omega
  rw [hr, v.ord_mul hbne h0, hb0, zero_add]

end Assembly

end D4A1
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne.D4A1"

set_option maxHeartbeats 25600000 in
open ModularCurve.NodeLocalized in
open D4A1 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P₁ : PlaceSpecialization A q 1 data hKr k red hα₁ hβ₁}
    (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q) (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)
    (c₀ : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ c : R.NodeCoordinates K w,
      Ideal.span {R.nodeConst K w ϖ, c.x} = Ideal.span {R.nodeConst K w ϖ, c₀.x} ∧
      Ideal.span {R.nodeConst K w ϖ, c.y} = Ideal.span {R.nodeConst K w ϖ, c₀.y} ∧
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)), 1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  classical

  have hw' := hW w hw
  have hss : a ∈ ssJSet q k := by
    have h := ((isSupersingularPlace_iff q 1 k w).mp hw').2.2
    rwa [ha] at h
  have ha2 : a ^ (q ^ 2) = a := pow_q_sq_eq_self_of_mem_ssJSet q hss

  obtain ⟨-, hlocal, -, -⟩ := ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hlocal
  obtain ⟨eK, ε, heK, hε, hqϖ, G', H', wU, hwU, hGH, hmax, hpr1, hpr2, hnm1, hnm2, hsp1, hsp2⟩ :=
    exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring red a hss ha2 hq K x hx ϖ hϖ
  have hmax' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = _ := hmax

  let e := qExpIso R hmodel W hW hreg K w hw a ha x hx
  have heϖ : e (R.nodeConst K w ϖ) = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := qExpIso_nodeConst R hmodel W hW hreg K w hw a ha x hx ϖ
  have heϖ' : e.symm (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) = R.nodeConst K w ϖ := by rw [← heϖ, e.symm_apply_apply]
  set ϖS := R.nodeConst K w ϖ with hϖS
  set xS := e.symm G' with hxS
  set yS := e.symm H' with hyS

  have hspx : Ideal.span {ϖS, xS} = Ideal.map (e.symm : _ →+* _) (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}) := by
    rw [Transport.map_symm_span_pair, heϖ']
  have hspy : Ideal.span {ϖS, yS} = Ideal.map (e.symm : _ →+* _) (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}) := by
    rw [Transport.map_symm_span_pair, heϖ']
  have hspm : Ideal.span {ϖS, xS, yS} = Ideal.map (e.symm : _ →+* _) (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'}) := by
    rw [Transport.map_symm_span_triple, heϖ']

  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hK1 := nodeResidue₁_eq_zero_iff R hmodel W hW hreg K w hw a ha x hx ϖ hϖ
  have hK2 := nodeResidue₂_eq_zero_iff R hmodel W hW hreg K w hw a ha x hx ϖ hϖ

  set GS := e.symm (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hGS
  set HS := e.symm (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hHS

  have hspxG : Ideal.span {ϖS, xS} = Ideal.span {ϖS, GS} := by
    rw [hspx, hsp1, Transport.map_symm_span_pair, heϖ']
  have hspyH : Ideal.span {ϖS, yS} = Ideal.span {ϖS, HS} := by
    rw [hspy, hsp2, Transport.map_symm_span_pair, heϖ']

  have hϖ₁ : R.nodeResidue₁ w ⟨ϖS, ϖS.2.1⟩ = 0 :=
    (hK1 ϖS).mpr (by rw [heϖ]; exact Ideal.subset_span (Set.mem_insert _ _))
  have hϖ₂ : R.nodeResidue₂ w ⟨ϖS, ϖS.2.1⟩ = 0 :=
    (hK2 ϖS).mpr (by rw [heϖ]; exact Ideal.subset_span (Set.mem_insert _ _))
  have hx₁ : R.nodeResidue₁ w ⟨xS, xS.2.1⟩ = 0 := (hK1 xS).mpr (by
    rw [hxS, e.apply_symm_apply, ← hsp1]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hy₂ : R.nodeResidue₂ w ⟨yS, yS.2.1⟩ = 0 := (hK2 yS).mpr (by
    rw [hyS, e.apply_symm_apply, ← hsp2]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hreg' := ord_nodeResidue_nonneg R hmodel W hW hreg K w hw a ha x hx ϖ hϖ

  haveI hlocS : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.of_surjective' (e.symm : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥(R.nodeIntegersOver K w)) e.symm.surjective
  have hmaxS : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {ϖS, xS, yS} :=
    (Transport.eq_map_symm_of_isMaximal_of_maximalIdeal_eq e hmax' _
      (IsLocalRing.maximalIdeal.isMaximal _)).trans hspm.symm

  have hwpl : w = charLGeomPlaceOfPoint k a := by
    have hpos := ModularCurve.ord_sub_evalAt_pos_of_isRational ((isSupersingularPlace_iff q 1 k w).mp hw').1
      ((isSupersingularPlace_iff q 1 k w).mp hw').2.1.1 (jGeomGen_sub_algebraMap_ne_zero k 1 _)
    rw [ha] at hpos
    exact eq_charLGeomPlaceOfPoint_of_ord_pos hpos
  have hφw : arithFrobC q k 1 • w = charLGeomPlaceOfPoint k (a ^ q) := by
    rw [hwpl]; exact arithFrobC_smul_charLGeomPlaceOfPoint q a

  have hordH : w.ord (R.nodeResidue₁ w ⟨HS, HS.2.1⟩) = 1 := by
    have hHF1 : ((HS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers := HS.2.1.1
    have hloc : ((((HS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
      (R.mem_integersFst_iff _).mp hHF1
    obtain ⟨h, hres⟩ := R.residue₁_eq_modularRedLocHom _ hloc
    have hcoe : ((((HS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))) : LaurentSeries (AlgebraicClosure ℚ)) = (((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hHS]; exact coe_coe_qExpIso_symm R hmodel W hW hreg K w hw a ha x hx _
    have h₁ : ((((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ))) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := hcoe ▸ hloc
    have hsub : (⟨_, h₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hloc⟩ := Subtype.ext hcoe.symm
    have h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1 := by
      rw [hsub, ← hres]; exact (R.ι (R.R₁.residue ⟨_, h⟩)).2
    have h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := by
      intro h0
      have hmem := (modularRedLocHom_eq_zero_iff_mem_span_branchFst red a ha2 K ϖ hϖ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) h₁).mp h0
      apply hnm1
      have hle : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ≤ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
        rw [Ideal.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Ideal.subset_span (Set.mem_insert _ _)
        · exact hmem
      rw [← hsp1, ← hsp2] at hle
      exact hle (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have h2c := (ord_modularRedLocHom_eq_iff_exists_isUnit red a ha2 K ϖ hϖ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) h₁ h₁F h0 1).mpr
      ⟨1, isUnit_one, by rw [pow_one, mul_one, sub_self]; exact zero_mem _⟩
    have hel : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = R.nodeResidue₁ w ⟨HS, HS.2.1⟩ := by
      apply Subtype.ext
      rw [nodeResidue₁_apply, residue₁_apply]
      change CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = ((R.ι (R.R₁.residue ⟨((HS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), h⟩) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
      rw [hres, hsub]
    rw [frobNodePair_fst, hel, ← hwpl] at h2c
    exact_mod_cast h2c

  have hordG : (arithFrobC q k 1 • w).ord (R.nodeResidue₂ w ⟨GS, GS.2.1⟩) = 1 := by
    obtain ⟨σ, hσcoe, hσeval⟩ := exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar red a ha2 K
    have ha2' : (a ^ q) ^ (q ^ 2) = a ^ q := by rw [← pow_mul, mul_comm, pow_mul, ha2]
    have hGF2 : ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₂.integers := GS.2.1.2.1
    have hloc2 : ((atkinLehnerBar 1 q ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red := (R.mem_integersSnd_iff _).mp hGF2
    obtain ⟨h, hres⟩ := R.residue₁_eq_modularRedLocHom _ hloc2
    have hcoeG : ((((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))) : LaurentSeries (AlgebraicClosure ℚ)) = (((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hGS]; exact coe_coe_qExpIso_symm R hmodel W hW hreg K w hw a ha x hx _
    have hgF : ((((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ))) ∈ modularFunctionFieldBar (1 * q) := hcoeG ▸ ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))).2
    have heqG : (⟨(((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : ↥(modularFunctionFieldBar (1 * q))) = ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) := Subtype.ext hcoeG.symm
    have hAL : atkinLehnerBar 1 q ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) = frickeInvolutionBar (1 * q) ⟨(((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ := by
      rw [atkinLehnerBar_one_eq, heqG]
    have hσG : σ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) := by
      have hev := hσeval (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
      have hren : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q : MvPolynomial (Fin 2) ↥(coeffSubring A K)) =
          MvPolynomial.X 0 - MvPolynomial.X 1 ^ q := by
        simp [MvPolynomial.rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hren] at hev
      exact hev
    have hfr : ((σ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((frickeInvolutionBar (1 * q) ⟨(((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
      hσcoe _ hgF
    have hcoeB : (((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)))) : LaurentSeries (AlgebraicClosure ℚ)) = ((atkinLehnerBar 1 q ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← hσG, hfr, ← hAL]
    have h₁ : ((((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)))) : LaurentSeries (AlgebraicClosure ℚ))) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := hcoeB ▸ hloc2
    have hsub : (⟨_, h₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hloc2⟩ := Subtype.ext hcoeB
    have h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1 := by
      rw [hsub, ← hres]; exact (R.ι (R.R₁.residue ⟨_, h⟩)).2
    have hel : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = R.nodeResidue₂ w ⟨GS, GS.2.1⟩ := by
      apply Subtype.ext
      rw [nodeResidue₂_apply, residue₂_apply, R.residue₂_eq]
      change CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = ((R.ι (R.R₁.residue ⟨atkinLehnerBar 1 q ((GS : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), h⟩) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
      rw [hres, hsub]
    have hres2ne : R.nodeResidue₂ w ⟨GS, GS.2.1⟩ ≠ 0 := by
      intro h0
      have hmem := (hK2 GS).mp h0
      rw [hGS, (qExpIso R hmodel W hW hreg K w hw a ha x hx).apply_symm_apply] at hmem
      apply hnm2
      have hle : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ≤ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
        rw [Ideal.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Ideal.subset_span (Set.mem_insert _ _)
        · exact hmem
      rw [← hsp1, ← hsp2] at hle
      exact hle (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := fun h0 => hres2ne (by rw [← hel]; exact Subtype.ext h0)
    have h2c := (ord_modularRedLocHom_eq_iff_exists_isUnit red (a ^ q) ha2' K ϖ hϖ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) h₁ h₁F h0 1).mpr
      ⟨1, isUnit_one, by rw [pow_one, mul_one, sub_self]; exact zero_mem _⟩
    rw [frobNodePair_fst, hel, ← hφw] at h2c
    exact_mod_cast h2c

  have ord₂_eq_of_span_eq : ∀ {r r₀ : ↥(R.nodeIntegersOver K w)},
      Ideal.span {ϖS, r} = Ideal.span {ϖS, r₀} → res₂S R K w r₀ ≠ 0 →
      (arithFrobC q k 1 • w).ord (res₂S R K w r) = (arithFrobC q k 1 • w).ord (res₂S R K w r₀) := by
    intro r r₀ hsp h0
    have hmem : r ∈ Ideal.span {ϖS, r₀} := hsp ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hmem' : r₀ ∈ Ideal.span {ϖS, r} := hsp.symm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hmem
    obtain ⟨α', β', hαβ'⟩ := Ideal.mem_span_pair.mp hmem'
    have h1 : res₂S R K w r = res₂S R K w β * res₂S R K w r₀ := by
      conv_lhs => rw [← hαβ]
      rw [map_add, map_mul, map_mul, res₂S_apply R K w ϖS, hϖ₂, mul_zero, zero_add]
    have h2 : res₂S R K w r₀ = res₂S R K w β' * res₂S R K w r := by
      conv_lhs => rw [← hαβ']
      rw [map_add, map_mul, map_mul, res₂S_apply R K w ϖS, hϖ₂, mul_zero, zero_add]
    exact ord_eq_of_mutual _ h1 h2 h0 (hreg' β).2 (hreg' β').2
  have ord₁_eq_of_span_eq : ∀ {r r₀ : ↥(R.nodeIntegersOver K w)},
      Ideal.span {ϖS, r} = Ideal.span {ϖS, r₀} → res₁S R K w r₀ ≠ 0 →
      w.ord (res₁S R K w r) = w.ord (res₁S R K w r₀) := by
    intro r r₀ hsp h0
    have hmem : r ∈ Ideal.span {ϖS, r₀} := hsp ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hmem' : r₀ ∈ Ideal.span {ϖS, r} := hsp.symm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hmem
    obtain ⟨α', β', hαβ'⟩ := Ideal.mem_span_pair.mp hmem'
    have h1 : res₁S R K w r = res₁S R K w β * res₁S R K w r₀ := by
      conv_lhs => rw [← hαβ]
      rw [map_add, map_mul, map_mul, res₁S_apply R K w ϖS, hϖ₁, mul_zero, zero_add]
    have h2 : res₁S R K w r₀ = res₁S R K w β' * res₁S R K w r := by
      conv_lhs => rw [← hαβ']
      rw [map_add, map_mul, map_mul, res₁S_apply R K w ϖS, hϖ₁, mul_zero, zero_add]
    exact ord_eq_of_mutual _ h1 h2 h0 (hreg' β).1 (hreg' β').1

  have hGS0 : res₂S R K w GS ≠ 0 := by
    intro h; have := hordG; rw [← res₂S_apply, h, Place.ord_zero] at this; exact zero_ne_one this
  have hHS0 : res₁S R K w HS ≠ 0 := by
    intro h; have := hordH; rw [← res₁S_apply, h, Place.ord_zero] at this; exact zero_ne_one this
  have hx₂ : (arithFrobC q k 1 • w).ord (R.nodeResidue₂ w ⟨xS, xS.2.1⟩) = 1 := by
    rw [← res₂S_apply, ord₂_eq_of_span_eq hspxG hGS0, res₂S_apply]; exact hordG
  have hy₁ : w.ord (R.nodeResidue₁ w ⟨yS, yS.2.1⟩) = 1 := by
    rw [← res₁S_apply, ord₁_eq_of_span_eq hspyH hHS0, res₁S_apply]; exact hordH
  have hxS0 : res₂S R K w xS ≠ 0 := by
    intro h; have := hx₂; rw [← res₂S_apply, h, Place.ord_zero] at this; exact zero_ne_one this
  have hyS0 : res₁S R K w yS ≠ 0 := by
    intro h; have := hy₁; rw [← res₁S_apply, h, Place.ord_zero] at this; exact zero_ne_one this

  have unit_of_ord₂_zero : ∀ β : ↥(R.nodeIntegersOver K w), res₂S R K w β ≠ 0 →
      (arithFrobC q k 1 • w).ord (res₂S R K w β) = 0 → IsUnit β := by
    intro β hβ0 hβord
    by_contra hnu
    have hβm : β ∈ Ideal.span {ϖS, xS, yS} := hmaxS ▸ (IsLocalRing.mem_maximalIdeal β).mpr hnu
    rw [Ideal.mem_span_insert] at hβm
    obtain ⟨a₁, z, hz, hβz⟩ := hβm
    obtain ⟨b₁, d₁, hbd⟩ := Ideal.mem_span_pair.mp hz
    have hres : res₂S R K w β = res₂S R K w b₁ * res₂S R K w xS := by
      rw [hβz, ← hbd, map_add, map_add, map_mul, map_mul, map_mul, res₂S_apply R K w ϖS, hϖ₂,
        res₂S_apply R K w yS, hy₂]
      ring
    by_cases hb : res₂S R K w b₁ = 0
    · exact hβ0 (by rw [hres, hb, zero_mul])
    · have h := congrArg ((arithFrobC q k 1 • w).ord) hres
      rw [Place.ord_mul _ hb hxS0, hβord, res₂S_apply R K w xS, hx₂] at h
      have := (hreg' b₁).2 (by rw [← res₂S_apply]; exact hb)
      rw [← res₂S_apply] at this
      omega
  have unit_of_ord₁_zero : ∀ β : ↥(R.nodeIntegersOver K w), res₁S R K w β ≠ 0 →
      w.ord (res₁S R K w β) = 0 → IsUnit β := by
    intro β hβ0 hβord
    by_contra hnu
    have hβm : β ∈ Ideal.span {ϖS, xS, yS} := hmaxS ▸ (IsLocalRing.mem_maximalIdeal β).mpr hnu
    rw [Ideal.mem_span_insert] at hβm
    obtain ⟨a₁, z, hz, hβz⟩ := hβm
    obtain ⟨b₁, d₁, hbd⟩ := Ideal.mem_span_pair.mp hz
    have hres : res₁S R K w β = res₁S R K w d₁ * res₁S R K w yS := by
      rw [hβz, ← hbd, map_add, map_add, map_mul, map_mul, map_mul, res₁S_apply R K w ϖS, hϖ₁,
        res₁S_apply R K w xS, hx₁]
      ring
    by_cases hd : res₁S R K w d₁ = 0
    · exact hβ0 (by rw [hres, hd, zero_mul])
    · have h := congrArg (w.ord) hres
      rw [Place.ord_mul _ hd hyS0, hβord, res₁S_apply R K w yS, hy₁] at h
      have := (hreg' d₁).1 (by rw [← res₁S_apply]; exact hd)
      rw [← res₁S_apply] at this
      omega
  have hbx : Ideal.span {ϖS, xS} = Ideal.span {ϖS, c₀.x} := by

    have hcx : c₀.x ∈ Ideal.span {ϖS, xS} := by
      have h := (hK1 c₀.x).mp c₀.x_fst
      rw [← hsp1] at h
      rw [hspx, Transport.mem_map_iff, RingEquiv.symm_symm]
      exact h
    apply le_antisymm
    ·
      obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hcx
      have hres : res₂S R K w c₀.x = res₂S R K w β * res₂S R K w xS := by
        rw [← hαβ, map_add, map_mul, map_mul, res₂S_apply R K w ϖS, hϖ₂, mul_zero, zero_add]
      have hcx0 : res₂S R K w c₀.x ≠ 0 := by rw [res₂S_apply]; exact c₀.nodeResidue₂_x_ne_zero
      have hβ0 : res₂S R K w β ≠ 0 := fun h => hcx0 (by rw [hres, h, zero_mul])
      have hβord : (arithFrobC q k 1 • w).ord (res₂S R K w β) = 0 := by
        have h := congrArg ((arithFrobC q k 1 • w).ord) hres
        rw [Place.ord_mul _ hβ0 hxS0, res₂S_apply R K w c₀.x, c₀.x_snd, res₂S_apply R K w xS, hx₂] at h
        omega
      obtain ⟨βu, hβu⟩ := unit_of_ord₂_zero β hβ0 hβord
      have hβx : (βu : ↥(R.nodeIntegersOver K w)) * xS = c₀.x - α * ϖS := by
        rw [hβu]; linear_combination hαβ
      have hxS' : xS = ↑βu⁻¹ * (c₀.x - α * ϖS) :=
        (Units.inv_mul_cancel_left βu xS).symm.trans (congrArg (fun t => (↑βu⁻¹ : ↥(R.nodeIntegersOver K w)) * t) hβx)
      have hmemx : xS ∈ Ideal.span {ϖS, c₀.x} := by
        rw [hxS']
        exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))))
      exact Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨Ideal.subset_span (Set.mem_insert _ _),
        Set.singleton_subset_iff.mpr hmemx⟩)
    · exact Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨Ideal.subset_span (Set.mem_insert _ _),
        Set.singleton_subset_iff.mpr hcx⟩)
  have hby : Ideal.span {ϖS, yS} = Ideal.span {ϖS, c₀.y} := by
    have hcy : c₀.y ∈ Ideal.span {ϖS, yS} := by
      have h := (hK2 c₀.y).mp c₀.y_snd
      rw [← hsp2] at h
      rw [hspy, Transport.mem_map_iff, RingEquiv.symm_symm]
      exact h
    apply le_antisymm
    · obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hcy
      have hres : res₁S R K w c₀.y = res₁S R K w β * res₁S R K w yS := by
        rw [← hαβ, map_add, map_mul, map_mul, res₁S_apply R K w ϖS, hϖ₁, mul_zero, zero_add]
      have hcy0 : res₁S R K w c₀.y ≠ 0 := by rw [res₁S_apply]; exact c₀.nodeResidue₁_y_ne_zero
      have hβ0 : res₁S R K w β ≠ 0 := fun h => hcy0 (by rw [hres, h, zero_mul])
      have hβord : w.ord (res₁S R K w β) = 0 := by
        have h := congrArg (w.ord) hres
        rw [Place.ord_mul _ hβ0 hyS0, res₁S_apply R K w c₀.y, c₀.y_fst, res₁S_apply R K w yS, hy₁] at h
        omega
      obtain ⟨βu, hβu⟩ := unit_of_ord₁_zero β hβ0 hβord
      have hβy : (βu : ↥(R.nodeIntegersOver K w)) * yS = c₀.y - α * ϖS := by
        rw [hβu]; linear_combination hαβ
      have hyS' : yS = ↑βu⁻¹ * (c₀.y - α * ϖS) :=
        (Units.inv_mul_cancel_left βu yS).symm.trans (congrArg (fun t => (↑βu⁻¹ : ↥(R.nodeIntegersOver K w)) * t) hβy)
      have hmemy : yS ∈ Ideal.span {ϖS, c₀.y} := by
        rw [hyS']
        exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))))
      exact Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨Ideal.subset_span (Set.mem_insert _ _),
        Set.singleton_subset_iff.mpr hmemy⟩)
    · exact Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨Ideal.subset_span (Set.mem_insert _ _),
        Set.singleton_subset_iff.mpr hcy⟩)

  refine ⟨⟨xS, yS, hx₁, hx₂, hy₂, hy₁⟩, hbx, hby, eK, ε, heK, hε, hqϖ, jWidth a * eK, e.symm wU,
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (jWidth_pos a).ne' (by omega)),
    (Transport.isUnit_symm_iff e wU).mpr hwU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply e.injective
    show e (xS * yS) = e (ϖS ^ (jWidth a * eK) * e.symm wU)
    rw [map_mul, map_mul, map_pow, hxS, hyS, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply, heϖ]
    exact hGH
  ·
    show (Ideal.span {ϖS, xS, yS}).IsMaximal
    rw [hspm, ← hmax']
    exact Transport.isMaximal_map_symm_maximalIdeal e
  · intro M hM
    show M = Ideal.span {ϖS, xS, yS}
    rw [hspm]
    exact Transport.eq_map_symm_of_isMaximal_of_maximalIdeal_eq e hmax' M hM
  · show (Ideal.span {ϖS, xS}).IsPrime
    rw [hspx]; exact (Transport.isPrime_map_iff e.symm _).mpr hpr1
  · show (Ideal.span {ϖS, yS}).IsPrime
    rw [hspy]; exact (Transport.isPrime_map_iff e.symm _).mpr hpr2
  · show yS ∉ Ideal.span {ϖS, xS}
    rw [hspx, hyS]; exact (Transport.apply_not_mem_map_iff e.symm _ H').mpr hnm1
  · show xS ∉ Ideal.span {ϖS, yS}
    rw [hspy, hxS]; exact (Transport.apply_not_mem_map_iff e.symm _ G').mpr hnm2

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne (solution)
