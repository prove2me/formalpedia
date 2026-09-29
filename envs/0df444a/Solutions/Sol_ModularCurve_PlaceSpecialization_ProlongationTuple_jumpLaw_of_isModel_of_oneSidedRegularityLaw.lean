-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.jumpLaw_of_isModel_of_oneSidedRegularityLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c3d0da2a-a39f-5d4a-bb6f-0db6516332fd

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_jumpLaw_of_isModel_of_oneSidedRegularityLaw
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide~IsCuspidal' ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem jl_smul_jFun (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • jFun N q = jFun N q :=
  Subtype.ext (by
    rw [ModularCurve.coe_arithmeticGalois_smul]
    exact ModularCurve.coeffMap_coeffEmb σ _)

private theorem jl_smul_jQFun (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • jQFun N q = jQFun N q :=
  Subtype.ext (by
    rw [ModularCurve.coe_arithmeticGalois_smul]
    exact ModularCurve.coeffMap_coeffEmb σ _)

private theorem jl_smul_tInfty (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • tInfty N q = tInfty N q := by
  show arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (jQFun N q / jFun N q ^ q) =
    jQFun N q / jFun N q ^ q
  rw [AlgebraicCurve.SemilinearAut.smul_def, map_div₀, map_pow, ← AlgebraicCurve.SemilinearAut.smul_def,
    ← AlgebraicCurve.SemilinearAut.smul_def, jl_smul_jQFun, jl_smul_jFun]

private theorem jl_smul_tZero (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • tZero N q = tZero N q := by
  show arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (jFun N q / jQFun N q ^ q) =
    jFun N q / jQFun N q ^ q
  rw [AlgebraicCurve.SemilinearAut.smul_def, map_div₀, map_pow, ← AlgebraicCurve.SemilinearAut.smul_def,
    ← AlgebraicCurve.SemilinearAut.smul_def, jl_smul_jFun, jl_smul_jQFun]

omit [Fact q.Prime] [NeZero N] in

private theorem jl_smul_algebraMap_inv_smul (σ' : ↥(A.decompositionSubgroup ℚ)) (a : A) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          ((σ'⁻¹ • a : A) : AlgebraicClosure ℚ) =
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
  rw [AlgebraicCurve.SemilinearAut.smul_algebraMap]
  exact congrArg _ (congrArg Subtype.val (smul_inv_smul σ' a))

private theorem jl_isCuspidal_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ' : ↥(A.decompositionSubgroup ℚ)) (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : IsCuspidal P c) :
    IsCuspidal P (arithmeticGalois (modularFunctionFieldFull (N * q))
      (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • c) := by
  intro a
  have key : jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) =
      arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
        (jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          ((σ'⁻¹ • a : A) : AlgebraicClosure ℚ)) := by
    rw [smul_sub, jl_smul_jFun, jl_smul_algebraMap_inv_smul]
  rw [key, AlgebraicCurve.SemilinearAut.ord_smul]
  exact h (σ'⁻¹ • a)

private theorem jl_isCuspidal'_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ' : ↥(A.decompositionSubgroup ℚ)) (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : IsCuspidal' P c) :
    IsCuspidal' P (arithmeticGalois (modularFunctionFieldFull (N * q))
      (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • c) := by
  intro a
  have key : jQFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) =
      arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
        (jQFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          ((σ'⁻¹ • a : A) : AlgebraicClosure ℚ)) := by
    rw [smul_sub, jl_smul_jQFun, jl_smul_algebraMap_inv_smul]
  rw [key, AlgebraicCurve.SemilinearAut.ord_smul]
  exact h (σ'⁻¹ • a)

private theorem jl_red_smul (P : PlaceSpecialization A q N data hKr k red hα hβ) (R : ProlongationTuple P)
    (σ' : ↥(A.decompositionSubgroup ℚ)) (hI : σ' ∈ A.inertiaSubgroup ℚ) (a : A) :
    red (σ' • a) = red a := by
  have h1 : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField A) σ' = 1 :=
    MonoidHom.mem_ker.mp hI
  have hx : σ' • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun h1 _
  rw [← R.redBar_residue, IsLocalRing.ResidueField.residue_smul, hx, R.redBar_residue]

private theorem jl_isInftySide_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (σ' : ↥(A.decompositionSubgroup ℚ)) (hI : σ' ∈ A.inertiaSubgroup ℚ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (h : IsInftySide P c) :
    IsInftySide P (arithmeticGalois (modularFunctionFieldFull (N * q))
      (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • c) := by
  obtain ⟨hcusp, τ, hτ, hv⟩ := h
  refine ⟨jl_isCuspidal_smul P σ' c hcusp, σ' • τ, (jl_red_smul P R σ' hI τ).trans hτ, ?_⟩

  have hbase : AlgebraicCurve.SemilinearAut.baseAut
        (arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
        (τ : AlgebraicClosure ℚ) =
      ((σ' • τ : A) : AlgebraicClosure ℚ) := rfl
  have hv' := hv.smul
    (arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  rw [jl_smul_tInfty, hbase] at hv'
  exact hv'

private theorem jl_isZeroSide_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (σ' : ↥(A.decompositionSubgroup ℚ)) (hI : σ' ∈ A.inertiaSubgroup ℚ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (h : IsZeroSide P c) :
    IsZeroSide P (arithmeticGalois (modularFunctionFieldFull (N * q))
      (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • c) := by
  obtain ⟨hcusp, τ, hτ, hv⟩ := h
  refine ⟨jl_isCuspidal'_smul P σ' c hcusp, σ' • τ, (jl_red_smul P R σ' hI τ).trans hτ, ?_⟩
  have hbase : AlgebraicCurve.SemilinearAut.baseAut
        (arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
        (τ : AlgebraicClosure ℚ) =
      ((σ' • τ : A) : AlgebraicClosure ℚ) := rfl
  have hv' := hv.smul
    (arithmeticGalois (modularFunctionFieldFull (N * q)) (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  rw [jl_smul_tZero, hbase] at hv'
  exact hv'

private theorem jl_isInftySide_smul_iff (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    IsInftySide P (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • c) ↔ IsInftySide P c := by
  obtain ⟨σ', hI, hσ'⟩ := Subgroup.mem_map.mp hσ
  obtain rfl : σ = ↑σ' := hσ'.symm
  refine ⟨fun h => ?_, jl_isInftySide_smul P R σ' hI c⟩

  have h' := jl_isInftySide_smul P R σ'⁻¹ (inv_mem hI) _ h
  rwa [Subgroup.coe_inv, map_inv, inv_smul_smul] at h'

private theorem jl_isZeroSide_smul_iff (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    IsZeroSide P (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • c) ↔ IsZeroSide P c := by
  obtain ⟨σ', hI, hσ'⟩ := Subgroup.mem_map.mp hσ
  obtain rfl : σ = ↑σ' := hσ'.symm
  refine ⟨fun h => ?_, jl_isZeroSide_smul P R σ' hI c⟩
  have h' := jl_isZeroSide_smul P R σ'⁻¹ (inv_mem hI) _ h
  rwa [Subgroup.coe_inv, map_inv, inv_smul_smul] at h'

private theorem jl_degree_mapDomain {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F'] (h : Place K F → Place K' F') (X : Divisor K F)
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1) :
    Divisor.degree (Finsupp.mapDomain h X) = Divisor.degree X := by
  induction X using Finsupp.induction with
  | zero => simp
  | single_add v n X _ _ ih =>
      rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
        AlgebraicCurve.Divisor.degree_single, AlgebraicCurve.Divisor.degree_single, hdeg, hdeg']

private theorem jl_degree_pos_of_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (X : Divisor K F) (hdeg : ∀ v : Place K F, v.deg = 1) (h0 : ∀ v, 0 ≤ X v)
    (v₀ : Place K F) (h1 : 0 < X v₀) : 0 < Divisor.degree X := by

  have hsum : AlgebraicCurve.Divisor.degree X = ∑ v ∈ X.support, X v := by
    simp only [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum,
      AddMonoidHom.coe_mulRight, hdeg, Nat.cast_one, mul_one]
  rw [hsum]
  exact Finset.sum_pos' (fun v _ => h0 v) ⟨v₀, Finsupp.mem_support_iff.mpr h1.ne', h1⟩

private theorem jl_degree_filter_smul_sub {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (E : Divisor K F) (Q : Place K F → Prop) [DecidablePred Q]
    (hQ : ∀ V, Q (g • V) ↔ Q V) : Divisor.degree ((g • E - E).filter Q) = 0 := by

  have hfilt : (g • E).filter Q = g • E.filter Q := by
    ext w
    have hw : Q w ↔ Q (g⁻¹ • w) := by rw [← hQ (g⁻¹ • w), smul_inv_smul]
    rw [Finsupp.filter_apply, AlgebraicCurve.SemilinearAut.divisor_smul_apply,
      AlgebraicCurve.SemilinearAut.divisor_smul_apply, Finsupp.filter_apply]
    by_cases hQw : Q w
    · rw [if_pos hQw, if_pos (hw.mp hQw)]
    · rw [if_neg hQw, if_neg (fun h => hQw (hw.mpr h))]
  rw [Finsupp.filter_sub, hfilt, map_sub, AlgebraicCurve.SemilinearAut.degree_smul, sub_self]

open Classical in

private theorem jl_filter_isStrictFst_add_filter_isStrictSnd
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hD : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) :
    D.filter P.IsStrictFst + D.filter P.IsStrictSnd = D := by
  ext W
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h1 : P.IsStrictFst W
  · by_cases h2 : P.IsStrictSnd W
    ·
      exact (h1.2 (by rw [h1.1]; exact h2.1.symm)).elim
    · rw [if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : P.IsStrictSnd W
    · rw [if_neg h1, if_pos h2, zero_add]
    · rw [if_neg h1, if_neg h2, add_zero]

      by_contra hne
      rcases hD W (Finsupp.mem_support_iff.mpr (Ne.symm hne)) with h | h
      · exact h1 h
      · exact h2 h

private theorem jl_isStrictFst_smul_iff (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) ↔ P.IsStrictFst V := by
  unfold PlaceSpecialization.IsStrictFst
  rw [ModularCurve.PlaceSpecialization.reduceFst_arithmeticGalois_smul P σ hσ V,
    ModularCurve.PlaceSpecialization.reduceSnd_arithmeticGalois_smul P σ hσ V]

private theorem jl_isStrictSnd_smul_iff (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) ↔ P.IsStrictSnd V := by
  unfold PlaceSpecialization.IsStrictSnd
  rw [ModularCurve.PlaceSpecialization.reduceFst_arithmeticGalois_smul P σ hσ V,
    ModularCurve.PlaceSpecialization.reduceSnd_arithmeticGalois_smul P σ hσ V]

private theorem jl_mapDomain_apply_eq_zero {α β M : Type*} [AddCommMonoid M] (h : α → β) (X : α →₀ M)
    (w : β) (hw : ∀ a ∈ X.support, h a ≠ w) : Finsupp.mapDomain h X w = 0 := by
  classical
  by_contra hne
  have hmem : w ∈ (Finsupp.mapDomain h X).support := Finsupp.mem_support_iff.mpr hne
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  exact hw a ha rfl

private theorem jl_filter_filter {α M : Type*} [AddCommMonoid M] (X : α →₀ M) (p₁ p₂ : α → Prop)
    [DecidablePred p₁] [DecidablePred p₂] [DecidablePred fun a => p₁ a ∧ p₂ a] :
    (X.filter p₁).filter p₂ = X.filter (fun a => p₁ a ∧ p₂ a) := by
  ext a
  simp only [Finsupp.filter_apply]
  by_cases h₁ : p₁ a <;> by_cases h₂ : p₂ a <;> simp [h₁, h₂]

private def jl_fixCuspFst (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst c)) = P.reduceFst c ∧
    ¬ IsAffineGeomPlace k N (P.reduceFst c)

private def jl_fixCuspSnd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c)) = P.reduceSnd c ∧
    ¬ IsAffineGeomPlace k N (P.reduceSnd c)

private def jl_QInfty (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsInftySide P c ∧ jl_fixCuspFst P c

private def jl_QInftyRest (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsInftySide P c ∧ ¬ jl_fixCuspFst P c

private def jl_QZero (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsZeroSide P c ∧ jl_fixCuspSnd P c

private def jl_QZeroRest (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsZeroSide P c ∧ ¬ jl_fixCuspSnd P c

private def jl_fixAff (_P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k N)) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v ∧ IsAffineGeomPlace k N v

private theorem jl_QInfty_smul_iff (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    jl_QInfty P (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • c) ↔ jl_QInfty P c := by
  unfold jl_QInfty jl_fixCuspFst
  rw [jl_isInftySide_smul_iff P R hσ c,
    ModularCurve.PlaceSpecialization.reduceFst_arithmeticGalois_smul P σ hσ c]

private theorem jl_QZero_smul_iff (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    jl_QZero P (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • c) ↔ jl_QZero P c := by
  unfold jl_QZero jl_fixCuspSnd
  rw [jl_isZeroSide_smul_iff P R hσ c,
    ModularCurve.PlaceSpecialization.reduceSnd_arithmeticGalois_smul P σ hσ c]

open Classical in

private theorem jl_filter_isInftySide_split (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    X.filter (IsInftySide P) = X.filter (jl_QInfty P) + X.filter (jl_QInftyRest P) := by
  ext c
  by_cases hA : IsInftySide P c <;> by_cases hB : jl_fixCuspFst P c <;>
    simp [jl_QInfty, jl_QInftyRest, hA, hB]

open Classical in

private theorem jl_filter_isZeroSide_split (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    X.filter (IsZeroSide P) = X.filter (jl_QZero P) + X.filter (jl_QZeroRest P) := by
  ext c
  by_cases hA : IsZeroSide P c <;> by_cases hB : jl_fixCuspSnd P c <;>
    simp [jl_QZero, jl_QZeroRest, hA, hB]

private theorem jl_reduceFst_not_fixed_of_strict (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V := by
  rcases hV with hV | hV
  · exact hV.2
  · intro hfix
    apply hV.2
    rw [hV.1] at hfix
    exact frobOnPlacesGeomLevel_injective k N data hKr hfix

private theorem jl_reduceSnd_not_fixed_of_strict (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V := by
  rcases hV with hV | hV
  · intro hfix
    apply hV.2
    rw [← hV.1] at hfix
    exact frobOnPlacesGeomLevel_injective k N data hKr hfix
  · exact hV.2

private theorem jl_ne_zero_of_residueFst_ne_zero {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hr₁ (by rw [show (⟨0, h₁⟩ : R.R₁.integers) = 0 from Subtype.ext (ZeroMemClass.coe_zero _).symm, map_zero])

private theorem jl_ne_zero_of_residueSnd_ne_zero {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers)
    (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hr₂ (by rw [show (⟨0, h₂⟩ : R.R₂.integers) = 0 from Subtype.ext (ZeroMemClass.coe_zero _).symm, map_zero])

private theorem jl_residue₁_ne_zero {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (x : R.R₁.integers) (h : R.R₁.residue x ≠ 0) : R.residue₁ x ≠ 0 := by
  rw [ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply]
  exact (map_ne_zero R.ι).mpr h

private theorem jl_residue₂_ne_zero {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (x : R.R₂.integers) (h : R.R₂.residue x ≠ 0) : R.residue₂ x ≠ 0 := by
  rw [ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply]
  exact (map_ne_zero R.ι).mpr h

private theorem jl_residue₁_eq_zero {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (x : R.R₁.integers) (h : R.R₁.residue x = 0) : R.residue₁ x = 0 := by
  rw [ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply]
  exact (congrArg R.ι h).trans (RingHom.map_zero R.ι)

private theorem jl_residue₂_eq_zero {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (x : R.R₂.integers) (h : R.R₂.residue x = 0) : R.residue₂ x = 0 := by
  rw [ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply]
  exact (congrArg R.ι h).trans (RingHom.map_zero R.ι)

private theorem jl_exists_principal_fst [IsAlgClosed k] {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (x : R.R₁.integers) (h : R.residue₁ x ≠ 0) :
    ∃ Dg : Divisor k (modularFunctionFieldC k N),
      (∀ v, Dg v = v.ord (R.residue₁ x)) ∧ Divisor.degree Dg = 0 := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  exact HasPrincipalDivisors.exists_divisor (K := k) (R.residue₁ x) h

private theorem jl_exists_principal_snd [IsAlgClosed k] {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (x : R.R₂.integers) (h : R.residue₂ x ≠ 0) :
    ∃ Dg : Divisor k (modularFunctionFieldC k N),
      (∀ v, Dg v = v.ord (R.residue₂ x)) ∧ Divisor.degree Dg = 0 := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  exact HasPrincipalDivisors.exists_divisor (K := k) (R.residue₂ x) h

private theorem jl_degree_eq_zero_of_full (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (g : SemilinearAut (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hdiv : ∀ V, D V + (g • E - E) V = V.ord f) : Divisor.degree D = 0 := by
  have hPD := (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor f hf
  obtain ⟨Df, hDf, hDf0⟩ := hPD
  have hFDf : D + (g • E - E) = Df := Finsupp.ext fun V => by
    rw [Finsupp.add_apply, hdiv V, hDf V]
  have hdeg := congrArg Divisor.degree hFDf
  rw [hDf0, map_add, map_sub, SemilinearAut.degree_smul, sub_self, add_zero] at hdeg
  exact hdeg

private theorem jl_osrl [IsAlgClosed k] [DecidableEq k] (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (R : ProlongationTuple P)
    (hOS : R.OneSidedRegularityLaw W)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f) :
    (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
      (∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ = 0 →
          0 < (s.1).ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N)) ∧
        (R.residue₂ ⟨f, h₂⟩ ≠ 0 → R.residue₁ ⟨f, h₁⟩ = 0 →
          0 < (s.2).ord (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N))) :=
  hOS f h₁ h₂ σ hσ D E hstrict hdiv

open Classical in

private theorem jl_S1_fst (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (f : modularFunctionFieldBar (N * q))
    (h₁ : f ∈ R.R₁.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (F : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hF : ∀ W, F W = W.ord f) :
    ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      Finsupp.mapDomain P.reduceFst (F.filter P.IsStrictFst) v = v.ord (R.residue₁ ⟨f, h₁⟩) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided hqN P R hmodel f h₁ hr₁ F hF

open Classical in

private theorem jl_S2_fst (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (f : modularFunctionFieldBar (N * q))
    (h₁ : f ∈ R.R₁.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (F : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hF : ∀ W, F W = W.ord f) :
    ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsInftySide P c →
      Finsupp.mapDomain P.reduceFst (F.filter (IsInftySide P)) (P.reduceFst c) = (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided hqN P R hmodel f h₁ hr₁ F hF

open Classical in

private theorem jl_decomp_fst [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (F : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (Dg : Divisor k (modularFunctionFieldC k N))
    (g : modularFunctionFieldC k N) (hDg : ∀ v, Dg v = v.ord g)
    (S1 : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      Finsupp.mapDomain P.reduceFst (F.filter P.IsStrictFst) v = v.ord g)
    (S2 : ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsInftySide P c →
      Finsupp.mapDomain P.reduceFst (F.filter (IsInftySide P)) (P.reduceFst c) = (P.reduceFst c).ord g) :
    Dg = Finsupp.mapDomain P.reduceFst (F.filter P.IsStrictFst) +
      Finsupp.mapDomain P.reduceFst (F.filter (jl_QInfty P)) + Dg.filter (jl_fixAff P) := by

  have hT1 : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      Finsupp.mapDomain P.reduceFst (F.filter P.IsStrictFst) v = 0 := by
    intro v hv
    refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
    have hsc : P.IsStrictFst c := (Finset.mem_filter.mp hc).2
    apply hsc.2
    rw [hcv]
    exact hv
  have hT2a : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      Finsupp.mapDomain P.reduceFst (F.filter (jl_QInfty P)) v = 0 := by
    intro v hv
    refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
    have hsc : jl_QInfty P c := (Finset.mem_filter.mp hc).2
    apply hv
    rw [← hcv]
    exact hsc.2.1
  have hT2b : ∀ v : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N v →
      Finsupp.mapDomain P.reduceFst (F.filter (jl_QInfty P)) v = 0 := by
    intro v hv
    refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
    have hsc : jl_QInfty P c := (Finset.mem_filter.mp hc).2
    apply hsc.2.2
    rw [hcv]
    exact hv
  have hT2c : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      ¬ IsAffineGeomPlace k N v →
      Finsupp.mapDomain P.reduceFst (F.filter (jl_QInfty P)) v = Dg v := by
    intro v hv hva
    have hcov :=
      (ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
        hqN P v hva).1
    obtain ⟨C, hC, hCv⟩ := hcov
    have h2 := S2 C hC
    rw [hCv, jl_filter_isInftySide_split P F, Finsupp.mapDomain_add, Finsupp.add_apply] at h2
    have hrest : Finsupp.mapDomain P.reduceFst (F.filter (jl_QInftyRest P)) v = 0 := by
      refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
      have hsc : jl_QInftyRest P c := (Finset.mem_filter.mp hc).2
      apply hsc.2
      refine ⟨?_, ?_⟩
      · rw [hcv]
        exact hv
      · rw [hcv]
        exact hva
    rw [hrest, add_zero] at h2
    rw [h2, hDg v]
  ext v
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
  · by_cases hva : IsAffineGeomPlace k N v
    · rw [hT1 v hv, hT2b v hva, if_pos (show jl_fixAff P v from ⟨hv, hva⟩), zero_add, zero_add]
    · rw [hT1 v hv, hT2c v hv hva, if_neg (show ¬ jl_fixAff P v from fun h => hva h.2), zero_add, add_zero]
  · rw [S1 v hv, hT2a v hv, if_neg (show ¬ jl_fixAff P v from fun h => hv h.1), hDg v, add_zero, add_zero]

open Classical in

private theorem jl_degStrict_fst [IsAlgClosed k] (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor.degree (Finsupp.mapDomain P.reduceFst
        ((D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E)).filter P.IsStrictFst)) =
      Divisor.degree (D.filter P.IsStrictFst) := by
  have hdegC : ∀ w : Place k (modularFunctionFieldC k N), w.deg = 1 :=
    ModularCurve.place_deg_eq_one_of_isAlgClosed k N
  have hdegB : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), V.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q)
  rw [jl_degree_mapDomain _ _ hdegB hdegC, Finsupp.filter_add, map_add,
    jl_degree_filter_smul_sub (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E P.IsStrictFst
      (fun V => jl_isStrictFst_smul_iff P hσ V), add_zero]

open Classical in

private theorem jl_degCusp_fst [IsAlgClosed k] (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) :
    Divisor.degree (Finsupp.mapDomain P.reduceFst
        ((D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E)).filter (jl_QInfty P))) = 0 := by
  have hdegC : ∀ w : Place k (modularFunctionFieldC k N), w.deg = 1 :=
    ModularCurve.place_deg_eq_one_of_isAlgClosed k N
  have hdegB : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), V.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q)
  have hDfix : ∀ V ∈ D.support,
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V :=
    fun V hV => jl_reduceFst_not_fixed_of_strict P V (hstrict V hV)
  have hD0 : D.filter (jl_QInfty P) = 0 :=
    (Finsupp.filter_eq_zero_iff _ _).mpr fun V hV => by
      by_contra hDV
      exact hDfix V (Finsupp.mem_support_iff.mpr hDV) hV.2.1
  rw [jl_degree_mapDomain _ _ hdegB hdegC, Finsupp.filter_add, hD0, zero_add]
  exact jl_degree_filter_smul_sub (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E (jl_QInfty P)
    (fun V => jl_QInfty_smul_iff P R hσ V)

open Classical in

private theorem jl_pos_fst [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
    (h₂ : f ∈ R.R₂.integers)
    (hOS1 : ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)))
    (hOS2 : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ = 0 →
          0 < (s.1).ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N)) ∧
        (R.residue₂ ⟨f, h₂⟩ ≠ 0 → R.residue₁ ⟨f, h₁⟩ = 0 →
          0 < (s.2).ord (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N)))
    (Dg : Divisor k (modularFunctionFieldC k N)) (hDg : ∀ v, Dg v = v.ord (R.residue₁ ⟨f, h₁⟩))
    (hr₁' : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hr₂' : R.residue₂ ⟨f, h₂⟩ = 0) :
    0 < Divisor.degree (Dg.filter (jl_fixAff P)) := by
  have hdegC : ∀ w : Place k (modularFunctionFieldC k N), w.deg = 1 :=
    ModularCurve.place_deg_eq_one_of_isAlgClosed k N
  have hne := ModularCurve.ssPlaces_nonempty q N hqN k
  obtain ⟨w₀, hw₀⟩ := hne
  have hss : IsSupersingularPlace q N k w₀ := hw₀
  have hfix₀ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w₀) = w₀ :=
    ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN
      data hKr w₀ hw₀
  have hs₀ : (w₀, arithFrobC q k N • w₀) ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
    (mem_nodePairsOfPlaces_iff _ _ _).mpr ⟨w₀, (hW w₀).mpr hw₀, rfl⟩
  have hord₀ : 0 < w₀.ord (R.residue₁ ⟨f, h₁⟩) := (hOS2 _ hs₀).1 hr₁' hr₂'
  refine jl_degree_pos_of_nonneg _ hdegC (fun v => ?_) w₀ ?_
  · rw [Finsupp.filter_apply]
    split_ifs with hv
    · rw [hDg v]
      exact (hOS1 v hv.1 hv.2).1 hr₁'
    · exact le_rfl
  · rw [Finsupp.filter_apply, if_pos (show jl_fixAff P w₀ from ⟨hfix₀, hss.2.1⟩), hDg w₀]
    exact hord₀

open Classical in

private theorem jl_clause_fst_core [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hOS : R.OneSidedRegularityLaw W)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hr₁' : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hr₂' : R.residue₂ ⟨f, h₂⟩ = 0)
    (Dg : Divisor k (modularFunctionFieldC k N)) (hDg : ∀ v, Dg v = v.ord (R.residue₁ ⟨f, h₁⟩))
    (hDg0 : Divisor.degree Dg = 0) (hdegD : Divisor.degree D = 0) :
    0 < Divisor.degree (D.filter P.IsStrictSnd) := by
  have hF : ∀ V, (D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E)) V = V.ord f := fun V => by
    rw [Finsupp.add_apply]
    exact hdiv V
  have S1 := jl_S1_fst hqN P R hmodel f h₁ hr₁ _ hF
  have S2 := jl_S2_fst hqN P R hmodel f h₁ hr₁ _ hF
  have hOS' := jl_osrl P W R hOS f h₁ h₂ hσ D E hstrict hdiv
  obtain ⟨hOS1, hOS2⟩ := hOS'
  have hdec := jl_decomp_fst hqN P _ Dg _ hDg S1 S2
  have e1 := jl_degStrict_fst P hσ D E
  have e2 := jl_degCusp_fst P R hσ D E hstrict
  have e3 := jl_pos_fst hqN P W hW R f h₁ h₂ hOS1 hOS2 Dg hDg hr₁' hr₂'
  have hcount := congrArg Divisor.degree hdec
  rw [map_add, map_add, e1, e2, add_zero, hDg0] at hcount
  have hsum := congrArg Divisor.degree (jl_filter_isStrictFst_add_filter_isStrictSnd P D hstrict)
  rw [map_add] at hsum
  omega

open Classical in

private theorem jl_clause_fst [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hOS : R.OneSidedRegularityLaw W)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ = 0) :
    0 < Divisor.degree (D.filter P.IsStrictSnd) := by
  have hf0 : f ≠ 0 := jl_ne_zero_of_residueFst_ne_zero R f h₁ hr₁
  have hr₁' : R.residue₁ ⟨f, h₁⟩ ≠ 0 := jl_residue₁_ne_zero R ⟨f, h₁⟩ hr₁
  have hr₂' : R.residue₂ ⟨f, h₂⟩ = 0 := jl_residue₂_eq_zero R ⟨f, h₂⟩ hr₂
  have hPD := jl_exists_principal_fst R ⟨f, h₁⟩ hr₁'
  obtain ⟨Dg, hDg, hDg0⟩ := hPD
  have hdegD : Divisor.degree D = 0 := jl_degree_eq_zero_of_full f hf0 D E _ hdiv
  exact jl_clause_fst_core hqN P W hW R hmodel hOS hσ f h₁ h₂ D E hstrict hdiv hr₁ hr₁' hr₂' Dg hDg hDg0
    hdegD

open Classical in

private theorem jl_S1_snd (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (f : modularFunctionFieldBar (N * q))
    (h₂ : f ∈ R.R₂.integers)
    (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) (F : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hF : ∀ W, F W = W.ord f) :
    ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      Finsupp.mapDomain P.reduceSnd (F.filter P.IsStrictSnd) v = v.ord (R.residue₂ ⟨f, h₂⟩) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided hqN P R hmodel f h₂ hr₂ F hF

open Classical in

private theorem jl_S2_snd (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (f : modularFunctionFieldBar (N * q))
    (h₂ : f ∈ R.R₂.integers)
    (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) (F : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hF : ∀ W, F W = W.ord f) :
    ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsZeroSide P c →
      Finsupp.mapDomain P.reduceSnd (F.filter (IsZeroSide P)) (P.reduceSnd c) = (P.reduceSnd c).ord (R.residue₂ ⟨f, h₂⟩) :=
  ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided hqN P R hmodel f h₂ hr₂ F hF

open Classical in

private theorem jl_decomp_snd [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (F : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (Dg : Divisor k (modularFunctionFieldC k N))
    (g : modularFunctionFieldC k N) (hDg : ∀ v, Dg v = v.ord g)
    (S1 : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      Finsupp.mapDomain P.reduceSnd (F.filter P.IsStrictSnd) v = v.ord g)
    (S2 : ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsZeroSide P c →
      Finsupp.mapDomain P.reduceSnd (F.filter (IsZeroSide P)) (P.reduceSnd c) = (P.reduceSnd c).ord g) :
    Dg = Finsupp.mapDomain P.reduceSnd (F.filter P.IsStrictSnd) +
      Finsupp.mapDomain P.reduceSnd (F.filter (jl_QZero P)) + Dg.filter (jl_fixAff P) := by

  have hT1 : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      Finsupp.mapDomain P.reduceSnd (F.filter P.IsStrictSnd) v = 0 := by
    intro v hv
    refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
    have hsc : P.IsStrictSnd c := (Finset.mem_filter.mp hc).2
    apply hsc.2
    rw [hcv]
    exact hv
  have hT2a : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      Finsupp.mapDomain P.reduceSnd (F.filter (jl_QZero P)) v = 0 := by
    intro v hv
    refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
    have hsc : jl_QZero P c := (Finset.mem_filter.mp hc).2
    apply hv
    rw [← hcv]
    exact hsc.2.1
  have hT2b : ∀ v : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N v →
      Finsupp.mapDomain P.reduceSnd (F.filter (jl_QZero P)) v = 0 := by
    intro v hv
    refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
    have hsc : jl_QZero P c := (Finset.mem_filter.mp hc).2
    apply hsc.2.2
    rw [hcv]
    exact hv
  have hT2c : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      ¬ IsAffineGeomPlace k N v →
      Finsupp.mapDomain P.reduceSnd (F.filter (jl_QZero P)) v = Dg v := by
    intro v hv hva
    have hcov :=
      (ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
        hqN P v hva).2
    obtain ⟨C, hC, hCv⟩ := hcov
    have h2 := S2 C hC
    rw [hCv, jl_filter_isZeroSide_split P F, Finsupp.mapDomain_add, Finsupp.add_apply] at h2
    have hrest : Finsupp.mapDomain P.reduceSnd (F.filter (jl_QZeroRest P)) v = 0 := by
      refine jl_mapDomain_apply_eq_zero _ _ _ (fun c hc hcv => ?_)
      have hsc : jl_QZeroRest P c := (Finset.mem_filter.mp hc).2
      apply hsc.2
      refine ⟨?_, ?_⟩
      · rw [hcv]
        exact hv
      · rw [hcv]
        exact hva
    rw [hrest, add_zero] at h2
    rw [h2, hDg v]
  ext v
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
  · by_cases hva : IsAffineGeomPlace k N v
    · rw [hT1 v hv, hT2b v hva, if_pos (show jl_fixAff P v from ⟨hv, hva⟩), zero_add, zero_add]
    · rw [hT1 v hv, hT2c v hv hva, if_neg (show ¬ jl_fixAff P v from fun h => hva h.2), zero_add, add_zero]
  · rw [S1 v hv, hT2a v hv, if_neg (show ¬ jl_fixAff P v from fun h => hv h.1), hDg v, add_zero, add_zero]

open Classical in

private theorem jl_degStrict_snd [IsAlgClosed k] (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor.degree (Finsupp.mapDomain P.reduceSnd
        ((D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E)).filter P.IsStrictSnd)) =
      Divisor.degree (D.filter P.IsStrictSnd) := by
  have hdegC : ∀ w : Place k (modularFunctionFieldC k N), w.deg = 1 :=
    ModularCurve.place_deg_eq_one_of_isAlgClosed k N
  have hdegB : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), V.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q)
  rw [jl_degree_mapDomain _ _ hdegB hdegC, Finsupp.filter_add, map_add,
    jl_degree_filter_smul_sub (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E P.IsStrictSnd
      (fun V => jl_isStrictSnd_smul_iff P hσ V), add_zero]

open Classical in

private theorem jl_degCusp_snd [IsAlgClosed k] (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) :
    Divisor.degree (Finsupp.mapDomain P.reduceSnd
        ((D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E)).filter (jl_QZero P))) = 0 := by
  have hdegC : ∀ w : Place k (modularFunctionFieldC k N), w.deg = 1 :=
    ModularCurve.place_deg_eq_one_of_isAlgClosed k N
  have hdegB : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), V.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q)
  have hDfix : ∀ V ∈ D.support,
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V :=
    fun V hV => jl_reduceSnd_not_fixed_of_strict P V (hstrict V hV)
  have hD0 : D.filter (jl_QZero P) = 0 :=
    (Finsupp.filter_eq_zero_iff _ _).mpr fun V hV => by
      by_contra hDV
      exact hDfix V (Finsupp.mem_support_iff.mpr hDV) hV.2.1
  rw [jl_degree_mapDomain _ _ hdegB hdegC, Finsupp.filter_add, hD0, zero_add]
  exact jl_degree_filter_smul_sub (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E (jl_QZero P)
    (fun V => jl_QZero_smul_iff P R hσ V)

open Classical in

private theorem jl_pos_snd [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
    (h₂ : f ∈ R.R₂.integers)
    (hOS1 : ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)))
    (hOS2 : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ = 0 →
          0 < (s.1).ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N)) ∧
        (R.residue₂ ⟨f, h₂⟩ ≠ 0 → R.residue₁ ⟨f, h₁⟩ = 0 →
          0 < (s.2).ord (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N)))
    (Dg : Divisor k (modularFunctionFieldC k N)) (hDg : ∀ v, Dg v = v.ord (R.residue₂ ⟨f, h₂⟩))
    (hr₂' : R.residue₂ ⟨f, h₂⟩ ≠ 0) (hr₁' : R.residue₁ ⟨f, h₁⟩ = 0) :
    0 < Divisor.degree (Dg.filter (jl_fixAff P)) := by
  have hdegC : ∀ w : Place k (modularFunctionFieldC k N), w.deg = 1 :=
    ModularCurve.place_deg_eq_one_of_isAlgClosed k N
  have hne := ModularCurve.ssPlaces_nonempty q N hqN k
  obtain ⟨w₀, hw₀⟩ := hne
  have hss : IsSupersingularPlace q N k w₀ := hw₀
  have hfix₀ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w₀) = w₀ :=
    ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN
      data hKr w₀ hw₀
  have hs₀ : (w₀, arithFrobC q k N • w₀) ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
    (mem_nodePairsOfPlaces_iff _ _ _).mpr ⟨w₀, (hW w₀).mpr hw₀, rfl⟩

  have hord₀ : 0 < (frobOnPlacesGeomLevel k N data hKr w₀).ord (R.residue₂ ⟨f, h₂⟩) := by
    rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w₀]
    exact (hOS2 _ hs₀).2 hr₂' hr₁'
  have hfix₀' : frobOnPlacesGeomLevel k N data hKr
      (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w₀)) =
        frobOnPlacesGeomLevel k N data hKr w₀ := by
    rw [hfix₀]
  have haff₀' : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr w₀) :=
    ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr w₀ hss.2.1
  refine jl_degree_pos_of_nonneg _ hdegC (fun v => ?_) (frobOnPlacesGeomLevel k N data hKr w₀) ?_
  · rw [Finsupp.filter_apply]
    split_ifs with hv
    ·
      have hfix' : frobOnPlacesGeomLevel k N data hKr
          (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v)) =
            frobOnPlacesGeomLevel k N data hKr v := by
        rw [hv.1]
      have haff' : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) :=
        ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr v hv.2
      have h := (hOS1 _ hfix' haff').2 hr₂'
      rw [hv.1] at h
      rw [hDg v]
      exact h
    · exact le_rfl
  · rw [Finsupp.filter_apply, if_pos (show jl_fixAff P (frobOnPlacesGeomLevel k N data hKr w₀) from
      ⟨hfix₀', haff₀'⟩), hDg]
    exact hord₀

open Classical in

private theorem jl_clause_snd_core [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hOS : R.OneSidedRegularityLaw W)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f)
    (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (hr₂' : R.residue₂ ⟨f, h₂⟩ ≠ 0) (hr₁' : R.residue₁ ⟨f, h₁⟩ = 0)
    (Dg : Divisor k (modularFunctionFieldC k N)) (hDg : ∀ v, Dg v = v.ord (R.residue₂ ⟨f, h₂⟩))
    (hDg0 : Divisor.degree Dg = 0) (hdegD : Divisor.degree D = 0) :
    0 < Divisor.degree (D.filter P.IsStrictFst) := by
  have hF : ∀ V, (D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E)) V = V.ord f := fun V => by
    rw [Finsupp.add_apply]
    exact hdiv V
  have S1 := jl_S1_snd hqN P R hmodel f h₂ hr₂ _ hF
  have S2 := jl_S2_snd hqN P R hmodel f h₂ hr₂ _ hF
  have hOS' := jl_osrl P W R hOS f h₁ h₂ hσ D E hstrict hdiv
  obtain ⟨hOS1, hOS2⟩ := hOS'
  have hdec := jl_decomp_snd hqN P _ Dg _ hDg S1 S2
  have e1 := jl_degStrict_snd P hσ D E
  have e2 := jl_degCusp_snd P R hσ D E hstrict
  have e3 := jl_pos_snd hqN P W hW R f h₁ h₂ hOS1 hOS2 Dg hDg hr₂' hr₁'
  have hcount := congrArg Divisor.degree hdec
  rw [map_add, map_add, e1, e2, add_zero, hDg0] at hcount
  have hsum := congrArg Divisor.degree (jl_filter_isStrictFst_add_filter_isStrictSnd P D hstrict)
  rw [map_add] at hsum
  omega

open Classical in

private theorem jl_clause_snd [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hOS : R.OneSidedRegularityLaw W)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f)
    (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) (hr₁ : R.R₁.residue ⟨f, h₁⟩ = 0) :
    0 < Divisor.degree (D.filter P.IsStrictFst) := by
  have hf0 : f ≠ 0 := jl_ne_zero_of_residueSnd_ne_zero R f h₂ hr₂
  have hr₂' : R.residue₂ ⟨f, h₂⟩ ≠ 0 := jl_residue₂_ne_zero R ⟨f, h₂⟩ hr₂
  have hr₁' : R.residue₁ ⟨f, h₁⟩ = 0 := jl_residue₁_eq_zero R ⟨f, h₁⟩ hr₁
  have hPD := jl_exists_principal_snd R ⟨f, h₂⟩ hr₂'
  obtain ⟨Dg, hDg, hDg0⟩ := hPD
  have hdegD : Divisor.degree D = 0 := jl_degree_eq_zero_of_full f hf0 D E _ hdiv
  exact jl_clause_snd_core hqN P W hW R hmodel hOS hσ f h₁ h₂ D E hstrict hdiv hr₂ hr₂' hr₁' Dg hDg hDg0
    hdegD

open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (hOS : R.OneSidedRegularityLaw W) :
    GaussJump.JumpLaw R := by
  intro σ hσ f h₁ h₂ D E hstrict hdiv
  exact ⟨fun hr₁ hr₂ => jl_clause_fst hqN P W hW R hmodel hOS hσ f h₁ h₂ D E hstrict hdiv hr₁ hr₂,
    fun hr₂ hr₁ => jl_clause_snd hqN P W hW R hmodel hOS hσ f h₁ h₂ D E hstrict hdiv hr₂ hr₁⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_jumpLaw_of_isModel_of_oneSidedRegularityLaw
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_jumpLaw_of_isModel_of_oneSidedRegularityLaw (solution)
