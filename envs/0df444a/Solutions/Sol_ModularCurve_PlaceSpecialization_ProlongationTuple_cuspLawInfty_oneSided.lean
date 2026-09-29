-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8d8d8b2c-5017-5f25-a473-a55d8259e3b1

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_divisor_oneSidedFst_laws_modularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_modularUnitSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided.ModularCurve"

noncomputable section
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple.atkinLehnerBar PlaceSpecialization.ProlongationTuple.IsInftySide PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_congr dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence qSeriesBar_algebraMap IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull frickeInvolutionBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull geomAut geomAut_coeffEmb coe_geomAut_coeffEmb deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_ne_zero coeff_modularUnitSeries_self PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero modularUnitSeries_mem_modularFunctionFieldFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_isFrickeAutFull_of_neZero frickeInvolutionBar_coeffEmb_modularUnitSeries"
p2m_open "ModularCurve"

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

theorem upkg_isAtkinLehnerAutFull (hqN : ¬ q ∣ N) :
    IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out) hqN)

theorem upkg_isFrickeAutFull : IsFrickeAutFull q (frickeInvolutionFull q) :=
  isFrickeAutFull_frickeInvolutionFull _ (exists_isFrickeAutFull_of_neZero q)

theorem upkg_mem_up {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull q) :
    x ∈ modularFunctionFieldFull (N * q) :=
  full_degeneracy_le (dvd_mul_left q N) hx

theorem upkg_coe_atkinLehner_incl (hqN : ¬ q ∣ N) {x : LaurentSeries ℚ}
    (hx : x ∈ modularFunctionFieldFull q) (hx' : x ∈ modularFunctionFieldFull (N * q)) :
    ((atkinLehnerInvolutionFull N q ⟨x, hx'⟩ : modularFunctionFieldFull (N * q)) : LaurentSeries ℚ)
      = ((frickeInvolutionFull q ⟨x, hx⟩ : modularFunctionFieldFull q) : LaurentSeries ℚ) := by
  have hAL := upkg_isAtkinLehnerAutFull N q hqN
  have hFr := upkg_isFrickeAutFull q
  set σ := atkinLehnerInvolutionFull N q with hσ
  set w := frickeInvolutionFull q with hw

  suffices H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull q),
      ∀ hy' : y ∈ modularFunctionFieldFull (N * q),
        ((σ ⟨y, hy'⟩ : modularFunctionFieldFull (N * q)) : LaurentSeries ℚ)
          = ((w ⟨y, hy⟩ : modularFunctionFieldFull q) : LaurentSeries ℚ) from H x hx hx'
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
    intro hy'
    obtain ⟨d, hd0, hdq, rfl⟩ := hy
    rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd d hdq with rfl | hd
    · have h1 := congrArg Subtype.val (hAL 1 inferInstance (one_dvd N)).1
      have h2 := congrArg Subtype.val (hFr 1 q (one_mul q) inferInstance inferInstance)
      simp only at h1 h2
      rw [h1, h2]
      exact qExpand_congr (one_mul q) jq
    · have hd' : q = d := hd.symm
      subst hd'
      have h1 := congrArg Subtype.val (hAL 1 inferInstance (one_dvd N)).2
      have h2 := congrArg Subtype.val (hFr q 1 (mul_one q) inferInstance inferInstance)
      simp only at h1 h2
      have e1 : (⟨qExpand ℚ q jq, hy'⟩ : modularFunctionFieldFull (N * q))
          = ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :=
        Subtype.ext (qExpand_congr (one_mul q).symm jq)
      rw [e1, h1, h2]
  | algebraMap c =>
    intro hy'
    have e1 : (⟨algebraMap ℚ (LaurentSeries ℚ) c, hy'⟩ : modularFunctionFieldFull (N * q))
        = ((c : ℚ) : modularFunctionFieldFull (N * q)) :=
      Subtype.ext (by rw [SubfieldClass.coe_ratCast]; exact eq_ratCast _ c)
    have e2 : (⟨algebraMap ℚ (LaurentSeries ℚ) c, IntermediateField.algebraMap_mem _ c⟩ :
        modularFunctionFieldFull q) = ((c : ℚ) : modularFunctionFieldFull q) :=
      Subtype.ext (by rw [SubfieldClass.coe_ratCast]; exact eq_ratCast _ c)
    rw [e1, e2, map_ratCast, map_ratCast, SubfieldClass.coe_ratCast, SubfieldClass.coe_ratCast]
  | add y z hy hz ihy ihz =>
    intro hyz'
    have e1 : (⟨y + z, hyz'⟩ : modularFunctionFieldFull (N * q))
        = ⟨y, upkg_mem_up N q hy⟩ + ⟨z, upkg_mem_up N q hz⟩ := rfl
    have e2 : (⟨y + z, add_mem hy hz⟩ : modularFunctionFieldFull q) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e1, e2, map_add, map_add, IntermediateField.coe_add, IntermediateField.coe_add,
      ihy (upkg_mem_up N q hy), ihz (upkg_mem_up N q hz)]
  | inv y hy ihy =>
    intro hy'
    have e1 : (⟨y⁻¹, hy'⟩ : modularFunctionFieldFull (N * q)) = ⟨y, upkg_mem_up N q hy⟩⁻¹ := rfl
    have e2 : (⟨y⁻¹, inv_mem hy⟩ : modularFunctionFieldFull q) = ⟨y, hy⟩⁻¹ := rfl
    rw [e1, e2, map_inv₀, map_inv₀, IntermediateField.coe_inv, IntermediateField.coe_inv,
      ihy (upkg_mem_up N q hy)]
  | mul y z hy hz ihy ihz =>
    intro hyz'
    have e1 : (⟨y * z, hyz'⟩ : modularFunctionFieldFull (N * q))
        = ⟨y, upkg_mem_up N q hy⟩ * ⟨z, upkg_mem_up N q hz⟩ := rfl
    have e2 : (⟨y * z, mul_mem hy hz⟩ : modularFunctionFieldFull q) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e1, e2, map_mul, map_mul, IntermediateField.coe_mul, IntermediateField.coe_mul,
      ihy (upkg_mem_up N q hy), ihz (upkg_mem_up N q hz)]

abbrev upkg_u0 : modularFunctionFieldFull q :=
  ⟨modularUnitSeries q, modularUnitSeries_mem_modularFunctionFieldFull q⟩

abbrev upkg_u : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (full_degeneracy_le (dvd_mul_left q N) (modularUnitSeries_mem_modularFunctionFieldFull q))⟩

theorem upkg_coe_atkinLehnerBar_u (hqN : ¬ q ∣ N) :
    ((PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q (upkg_u N q) :
        modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((q : AlgebraicClosure ℚ) ^ 12) • (coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))⁻¹ := by

  set u1 : modularFunctionFieldFull (N * q) :=
    ⟨modularUnitSeries q, upkg_mem_up N q (modularUnitSeries_mem_modularFunctionFieldFull q)⟩ with hu1
  have eu : upkg_u N q = ⟨coeffEmb (AlgebraicClosure ℚ) (u1 : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u1.2⟩ := rfl
  rw [PlaceSpecialization.ProlongationTuple.atkinLehnerBar, eu, coe_geomAut_coeffEmb, hu1,
    upkg_coe_atkinLehner_incl N q hqN (modularUnitSeries_mem_modularFunctionFieldFull q)]

  have hF := frickeInvolutionBar_coeffEmb_modularUnitSeries q
    (modularUnitSeries_mem_modularFunctionFieldFull q)
  rw [frickeInvolutionBar_def] at hF
  change ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull q) (frickeInvolutionFull q)
      ⟨coeffEmb (AlgebraicClosure ℚ) ((upkg_u0 q : modularFunctionFieldFull q) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (upkg_u0 q).2⟩ :
      modularFunctionFieldBar q) : LaurentSeries (AlgebraicClosure ℚ)) = _ at hF
  rw [coe_geomAut_coeffEmb] at hF
  exact hF

theorem upkg_coeffEmb_ne_zero (L : Type*) [Field L] [Algebra ℚ L] {x : LaurentSeries ℚ} (hx : x ≠ 0) :
    coeffEmb L x ≠ 0 := by
  intro h
  apply hx
  ext n
  have hn := congrArg (fun y : LaurentSeries L => y.coeff n) h
  simp only [coeffEmb_coeff, HahnSeries.coeff_zero] at hn
  exact (map_eq_zero_iff _ (algebraMap ℚ L).injective).mp hn

theorem upkg_u_ne_zero : upkg_u N q ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  exact upkg_coeffEmb_ne_zero (AlgebraicClosure ℚ) (modularUnitSeries_ne_zero q) h'

theorem upkg_atkinLehnerBar_u_mul_u (hqN : ¬ q ∣ N) :
    PlaceSpecialization.ProlongationTuple.atkinLehnerBar N q (upkg_u N q) * upkg_u N q
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          ((q : AlgebraicClosure ℚ) ^ 12) := by
  apply Subtype.ext
  have hne : coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q) ≠ 0 :=
    upkg_coeffEmb_ne_zero _ (modularUnitSeries_ne_zero q)
  have hR : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((q : AlgebraicClosure ℚ) ^ 12)
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          ((q : AlgebraicClosure ℚ) ^ 12) : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) := by
    have h := IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q)))
      (LaurentSeries (AlgebraicClosure ℚ)) ((q : AlgebraicClosure ℚ) ^ 12)
    rw [IntermediateField.algebraMap_apply] at h
    exact h
  rw [MulMemClass.coe_mul, upkg_coe_atkinLehnerBar_u N q hqN, ← HahnSeries.C_mul_eq_smul, mul_assoc,
    inv_mul_cancel₀ hne, mul_one, HahnSeries.C_apply]
  exact (qSeriesBar_algebraMap (L := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N * q))
    ((q : AlgebraicClosure ℚ) ^ 12)).symm

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple.atkinLehnerBar PlaceSpecialization.ProlongationTuple.IsInftySide PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_congr dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence qSeriesBar_algebraMap IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull frickeInvolutionBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull geomAut geomAut_coeffEmb coe_geomAut_coeffEmb deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_ne_zero coeff_modularUnitSeries_self PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero modularUnitSeries_mem_modularFunctionFieldFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_isFrickeAutFull_of_neZero frickeInvolutionBar_coeffEmb_modularUnitSeries"
namespace UpkgZ
p2m_open "ModularCurve"

p2m_open "HahnSeries ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided.ModularCurve"

theorem upkgZ_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext n
  rw [coeffMap_coeff]
  by_cases hdvd : (N : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N _ hdvd, qExpand_coeff_of_not_dvd N _ hdvd, map_zero]

theorem upkgZ_coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R u) = ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    rw [show n = (k : ℤ) by omega, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]

def upkgZ_delta : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit

def upkgZ_deltaInv : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem upkgZ_delta_mul_inv : upkgZ_delta * upkgZ_deltaInv = 1 := by
  have hη : HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit *
      HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv = 1 := by
    rw [← map_mul, dedekindEtaUnit_mul_inv]; exact map_one _
  have hs : (HahnSeries.single (1 : ℤ) 1 * HahnSeries.single (-1 : ℤ) 1 : LaurentSeries ℤ) = 1 := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, one_mul]; rfl
  unfold upkgZ_delta upkgZ_deltaInv
  rw [mul_mul_mul_comm, hs, hη, one_mul]

def upkgZ_unit (p : ℕ) [NeZero p] : LaurentSeries ℤ :=
  upkgZ_delta * qExpand ℤ p upkgZ_deltaInv

theorem upkgZ_coeffMap_rat_delta : coeffMap (Int.castRingHom ℚ) upkgZ_delta = deltaSeries := by
  rw [upkgZ_delta, map_mul, coeffMap_single, map_one, upkgZ_coeffMap_ofPowerSeries]
  rfl

theorem upkgZ_coeffMap_rat_unit (p : ℕ) [NeZero p] :
    coeffMap (Int.castRingHom ℚ) (upkgZ_unit p) = modularUnitSeries p := by
  have h1 : coeffMap (Int.castRingHom ℚ) (qExpand ℤ p upkgZ_delta) = deltaSeriesN p := by
    rw [upkgZ_coeffMap_qExpand, upkgZ_coeffMap_rat_delta]; rfl
  have hinv : coeffMap (Int.castRingHom ℚ) (qExpand ℤ p upkgZ_deltaInv) * deltaSeriesN p = 1 := by
    rw [← h1, ← map_mul, ← map_mul, mul_comm, upkgZ_delta_mul_inv, map_one, map_one]
  rw [upkgZ_unit, map_mul, upkgZ_coeffMap_rat_delta, modularUnitSeries,
    ← one_mul (deltaSeriesN p)⁻¹, ← hinv, mul_assoc,
    mul_inv_cancel₀ (deltaSeriesN_ne_zero p), mul_one, mul_comm]

theorem upkgZ_coeffEmb_modularUnitSeries_eq (L : Type*) [Field L] [Algebra ℚ L] (p : ℕ) [NeZero p] :
    coeffEmb L (modularUnitSeries p) = coeffMap (Int.castRingHom L) (upkgZ_unit p) := by
  rw [← upkgZ_coeffMap_rat_unit, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) _

end ModularCurve.UpkgZ

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple.atkinLehnerBar PlaceSpecialization.ProlongationTuple.IsInftySide PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_congr dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence qSeriesBar_algebraMap IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull frickeInvolutionBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull geomAut geomAut_coeffEmb coe_geomAut_coeffEmb deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_ne_zero coeff_modularUnitSeries_self PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero modularUnitSeries_mem_modularFunctionFieldFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_isFrickeAutFull_of_neZero frickeInvolutionBar_coeffEmb_modularUnitSeries"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.IsInftySide ProlongationTuple ProlongationTuple.residue₁_apply reduceFst ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar IsInftySide residue₁ residue₂ residue₁_apply IsModel R₁ ι mem_integersFst_iff R₂ residue₁_coeffMap mem_integersSnd_iff residue₂_eq exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero exists_divisor_oneSidedFst_laws_modularUnit"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization~IsInftySide ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem upkg_natCast_mem_maximalIdeal {q' : ℕ} [Fact q'.Prime] {A' : ValuationSubring (AlgebraicClosure ℚ)}
    {k' : Type*} [Field k'] [CharP k' q'] (red' : A' →+* k') : ((q' : ℕ) : A') ∈ maximalIdeal A' := by
  have hker : ((q' : ℕ) : A') ∈ RingHom.ker red' := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red') hker

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.upkg_residue₁_qpow (h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      ((q : AlgebraicClosure ℚ) ^ 12) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩ = 0 := by
  have hmem : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      ((((q : ℕ) : A) ^ 12 : A) : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    (R.R₁.algebraMap_mem_iff _).mpr (SetLike.coe_mem _)
  have e : (⟨_, h⟩ : R.R₁.integers) = ⟨_, hmem⟩ := Subtype.ext (by push_cast; rfl)
  rw [e, R.R₁.residue_algebraMap, map_pow, (IsLocalRing.residue_eq_zero_iff _).mpr
    (upkg_natCast_mem_maximalIdeal red), zero_pow (by norm_num), map_zero]

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "upkg_residue₁_qpow"

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.upkg_residue₂_u_eq_zero (hqN : ¬ q ∣ N) (h₁ : upkg_u N q ∈ R.R₁.integers)
    (hres₁ : R.R₁.residue ⟨upkg_u N q, h₁⟩ ≠ 0) :
    ∀ h₂ : upkg_u N q ∈ R.R₂.integers, R.R₂.residue ⟨upkg_u N q, h₂⟩ = 0 := by
  intro h₂
  rw [R.residue₂_eq (upkg_u N q) h₂]
  set hσ := (R.mem_integersFst_iff (atkinLehnerBar N q (upkg_u N q))).mpr
    ((R.mem_integersSnd_iff (upkg_u N q)).mp h₂)

  have hc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      ((q : AlgebraicClosure ℚ) ^ 12) ∈ R.R₁.integers := by
    have := mul_mem hσ h₁
    rwa [upkg_atkinLehnerBar_u_mul_u N q hqN] at this
  have hprod : (⟨atkinLehnerBar N q (upkg_u N q), hσ⟩ : R.R₁.integers) * ⟨upkg_u N q, h₁⟩
      = ⟨_, hc⟩ := Subtype.ext (by
    simp only [MulMemClass.coe_mul]
    exact upkg_atkinLehnerBar_u_mul_u N q hqN)
  have h0 := congrArg R.R₁.residue hprod
  rw [map_mul, R.upkg_residue₁_qpow hc] at h0
  exact (mul_eq_zero.mp h0).resolve_right hres₁

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "upkg_residue₂_u_eq_zero"

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.upkg_exists_mem_integers₁_residue_ne_zero :
    ∃ h₁ : upkg_u N q ∈ R.R₁.integers, R.R₁.residue ⟨upkg_u N q, h₁⟩ ≠ 0 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  set y : LaurentSeries A := coeffMap (Int.castRingHom A) (UpkgZ.upkgZ_unit q) with hy
  have hcoe : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q) := by
    rw [hy, coeffMap_coeffMap, UpkgZ.upkgZ_coeffEmb_modularUnitSeries_eq]
    exact coeffMap_congr (RingHom.ext_int _ _) _
  have hymem : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    rw [hcoe]; exact (upkg_u N q).2
  obtain ⟨h, hh⟩ := R.residue₁_coeffMap y hymem
  have e : (⟨coeffMap A.subtype y, hymem⟩ : modularFunctionFieldBar (N * q)) = upkg_u N q :=
    Subtype.ext hcoe
  refine ⟨e ▸ h, ?_⟩
  have e' : (⟨upkg_u N q, e ▸ h⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype y, hymem⟩, h⟩ := by
    apply Subtype.ext; exact e.symm
  rw [e']
  intro h0

  have hser : coeffMap (IsLocalRing.residue A) y = 0 :=
    hh.symm.trans (by simpa using congrArg Subtype.val h0)

  have hZ : (UpkgZ.upkgZ_unit q).coeff (1 - (q : ℤ)) = 1 := by
    have h1 := congrArg (fun z : LaurentSeries ℚ => z.coeff (1 - (q : ℤ))) (UpkgZ.upkgZ_coeffMap_rat_unit q)
    simp only [coeffMap_coeff, coeff_modularUnitSeries_self] at h1
    rw [eq_intCast] at h1
    exact_mod_cast h1
  have hc := congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff (1 - (q : ℤ))) hser
  rw [HahnSeries.coeff_zero, coeffMap_coeff, hy, coeffMap_coeff, hZ, map_one, map_one] at hc
  exact one_ne_zero hc

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "upkg_exists_mem_integers₁_residue_ne_zero"
end ModularCurve.PlaceSpecialization.ProlongationTuple

end

namespace CuspLawE2

section UnitZpow

variable {F : Type*} [Field F] (O : ValuationSubring F)

theorem inv_mem_of_isUnit {x : F} (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hxF : x * (w : F) = 1 := by
    have := congrArg (fun z : O => (z : F)) hw
    simpa using this
  have hx0 : x ≠ 0 := by
    rintro rfl; simp at hxF
  have : x⁻¹ = (w : F) := by
    rw [inv_eq_of_mul_eq_one_right hxF]
  rw [this]; exact w.2

theorem zpow_mem_of_isUnit {x : F} (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) (j : ℤ) : x ^ j ∈ O := by
  obtain ⟨n, rfl | rfl⟩ := j.eq_nat_or_neg
  · rw [zpow_natCast]; exact pow_mem hx n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem (inv_mem_of_isUnit O hx hu) n

theorem map_zpow_of_isUnit {K : Type*} [Field K] (φ : O →+* K) {x : F} (hx : x ∈ O)
    (hu : IsUnit (⟨x, hx⟩ : O)) (j : ℤ) :
    φ ⟨x ^ j, zpow_mem_of_isUnit O hx hu j⟩ = (φ ⟨x, hx⟩) ^ j := by
  obtain ⟨n, rfl | rfl⟩ := j.eq_nat_or_neg
  · have : (⟨x ^ ((n : ℕ) : ℤ), zpow_mem_of_isUnit O hx hu n⟩ : O) = ⟨x, hx⟩ ^ n :=
      Subtype.ext (by simp)
    rw [this, map_pow, zpow_natCast]
  ·
    have hinv : x⁻¹ ∈ O := inv_mem_of_isUnit O hx hu
    have hmul : (⟨x, hx⟩ : O) * ⟨x⁻¹, hinv⟩ = 1 := by
      apply Subtype.ext
      have hx0 : x ≠ 0 := by
        intro h0
        obtain ⟨w, hw⟩ := hu.exists_right_inv
        have := congrArg (fun z : O => (z : F)) hw
        simp [h0] at this
      simp [hx0]
    have hφinv : φ ⟨x⁻¹, hinv⟩ = (φ ⟨x, hx⟩)⁻¹ := by
      have h1 : φ ⟨x, hx⟩ * φ ⟨x⁻¹, hinv⟩ = 1 := by rw [← map_mul, hmul, map_one]
      exact (eq_inv_of_mul_eq_one_right h1)
    have : (⟨x ^ (-(n : ℤ)), zpow_mem_of_isUnit O hx hu (-(n:ℤ))⟩ : O) = ⟨x⁻¹, hinv⟩ ^ n :=
      Subtype.ext (by simp [zpow_neg, zpow_natCast, inv_pow])
    rw [this, map_pow, hφinv, zpow_neg, zpow_natCast, inv_pow]

end UnitZpow

section Linear

variable {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']

noncomputable def lawFun (r : Place K F → Place K' F') (S : Place K F → Prop) [DecidablePred S]
    (v : Place K' F') : Divisor K F →+ ℤ :=
  (Finsupp.applyAddHom v).comp ((Finsupp.mapDomain.addMonoidHom r).comp (Finsupp.filterAddHom S))

theorem lawFun_apply (r : Place K F → Place K' F') (S : Place K F → Prop) [DecidablePred S]
    (v : Place K' F') (D : Divisor K F) :
    lawFun r S v D = (Finsupp.mapDomain r (D.filter S)) v := rfl

end Linear

section Reduction

variable {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option maxHeartbeats 6400000 in
open Classical in

theorem cuspLawInfty_of_unit (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (u : modularFunctionFieldBar (N * q))
    (hu1 : u ∈ R.R₁.integers) (hures : R.R₁.residue ⟨u, hu1⟩ ≠ 0)
    (hudeg : ∀ h₂ : u ∈ R.R₂.integers, R.R₂.residue ⟨u, h₂⟩ = 0)
    (Du : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hDu : ∀ W, Du W = W.ord u)
    (hlawu : ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        PlaceSpecialization.ProlongationTuple.IsInftySide P c →
        Finsupp.mapDomain P.reduceFst (Du.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P))
          (P.reduceFst c) = (P.reduceFst c).ord (R.residue₁ ⟨u, hu1⟩))
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (hf : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hc : PlaceSpecialization.ProlongationTuple.IsInftySide P c) :
    Finsupp.mapDomain P.reduceFst (D.filter (PlaceSpecialization.ProlongationTuple.IsInftySide P))
        (P.reduceFst c) = (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩) := by

  set S := PlaceSpecialization.ProlongationTuple.IsInftySide P with hS
  set v := P.reduceFst c with hv
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hf
    have : (⟨(0 : modularFunctionFieldBar (N * q)), h₁⟩ : R.R₁.integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hures
    have : (⟨(0 : modularFunctionFieldBar (N * q)), hu1⟩ : R.R₁.integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]

  have hfU : IsUnit (⟨f, h₁⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hf
  have huU : IsUnit (⟨u, hu1⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hures

  obtain ⟨m, j, hm, h₂g, hres₂g⟩ :=
    PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
      R u hu0 hudeg f hf0

  have hujmem : u ^ j ∈ R.R₁.integers := zpow_mem_of_isUnit R.R₁.integers hu1 huU j
  have h₁g : f ^ m * u ^ j ∈ R.R₁.integers := mul_mem (pow_mem h₁ m) hujmem
  have hres₁g_eq : R.R₁.residue ⟨f ^ m * u ^ j, h₁g⟩
      = (R.R₁.residue ⟨f, h₁⟩) ^ m * (R.R₁.residue ⟨u, hu1⟩) ^ j := by
    have hsplit : (⟨f ^ m * u ^ j, h₁g⟩ : R.R₁.integers) = ⟨f, h₁⟩ ^ m * ⟨u ^ j, hujmem⟩ :=
      Subtype.ext (by simp)
    rw [hsplit, map_mul, map_pow, map_zpow_of_isUnit R.R₁.integers R.R₁.residue hu1 huU j]
  have hres₁g : R.R₁.residue ⟨f ^ m * u ^ j, h₁g⟩ ≠ 0 := by
    rw [hres₁g_eq]
    exact mul_ne_zero (pow_ne_zero _ hf) (zpow_ne_zero _ hures)

  let Dg : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) := (m : ℤ) • D + j • Du
  have hDg : ∀ W, Dg W = W.ord (f ^ m * u ^ j) := by
    intro W
    simp only [Dg, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hD W, hDu W]
    rw [Place.ord_mul W (pow_ne_zero _ hf0) (zpow_ne_zero _ hu0), ← zpow_natCast, Place.ord_zpow,
      Place.ord_zpow]

  have hlawg := hmodel.2.2.1 (f ^ m * u ^ j) h₁g h₂g hres₁g hres₂g Dg hDg c hc

  have hρf : R.residue₁ ⟨f, h₁⟩ ≠ 0 := by
    rw [PlaceSpecialization.ProlongationTuple.residue₁_apply]
    exact (map_ne_zero R.ι).mpr hf
  have hρu : R.residue₁ ⟨u, hu1⟩ ≠ 0 := by
    rw [PlaceSpecialization.ProlongationTuple.residue₁_apply]
    exact (map_ne_zero R.ι).mpr hures
  have hρg : R.residue₁ ⟨f ^ m * u ^ j, h₁g⟩ = (R.residue₁ ⟨f, h₁⟩) ^ m * (R.residue₁ ⟨u, hu1⟩) ^ j := by
    simp only [PlaceSpecialization.ProlongationTuple.residue₁_apply]
    rw [hres₁g_eq, map_mul, map_pow, map_zpow₀]
  have hordg : v.ord (R.residue₁ ⟨f ^ m * u ^ j, h₁g⟩)
      = (m : ℤ) * v.ord (R.residue₁ ⟨f, h₁⟩) + j * v.ord (R.residue₁ ⟨u, hu1⟩) := by
    rw [hρg, Place.ord_mul v (pow_ne_zero _ hρf) (zpow_ne_zero _ hρu), ← zpow_natCast, Place.ord_zpow,
      Place.ord_zpow]

  have hlin : (Finsupp.mapDomain P.reduceFst (Dg.filter S)) v
      = (m : ℤ) * (Finsupp.mapDomain P.reduceFst (D.filter S)) v
        + j * (Finsupp.mapDomain P.reduceFst (Du.filter S)) v := by
    have := (lawFun P.reduceFst S v).map_add ((m : ℤ) • D) (j • Du)
    rw [map_zsmul, map_zsmul] at this
    simpa only [lawFun_apply, smul_eq_mul, Dg] using this

  have hu' := hlawu c hc
  have key : (m : ℤ) * (Finsupp.mapDomain P.reduceFst (D.filter S)) v
      = (m : ℤ) * v.ord (R.residue₁ ⟨f, h₁⟩) := by
    have e1 := hlawg
    rw [hlin, hordg] at e1

    have e2 : (Finsupp.mapDomain P.reduceFst (Du.filter S)) v = v.ord (R.residue₁ ⟨u, hu1⟩) := hu'
    rw [e2] at e1
    linarith
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  exact mul_left_cancel₀ hm' key

end Reduction

end CuspLawE2

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide" in open CuspLawE2 _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided.ModularCurve.PlaceSpecialization.ProlongationTuple in
open Classical in

theorem solution {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          IsInftySide P c →
          Finsupp.mapDomain P.reduceFst (D.filter (IsInftySide P)) (P.reduceFst c)
            = (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩) := by
  intro f h₁ hf D hD c hc

  obtain ⟨hu1, hures⟩ := R.upkg_exists_mem_integers₁_residue_ne_zero
  have hudeg : ∀ h₂ : upkg_u N q ∈ R.R₂.integers, R.R₂.residue ⟨upkg_u N q, h₂⟩ = 0 :=
    R.upkg_residue₂_u_eq_zero hqN hu1 hures

  obtain ⟨Du, hDu, -, hlawu⟩ :=
    exists_divisor_oneSidedFst_laws_modularUnit hqN P R hmodel (upkg_u N q) rfl hu1
  exact cuspLawInfty_of_unit P R hmodel (upkg_u N q) hu1 hures hudeg Du hDu hlawu f h₁ hf D hD c hc

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided (solution)
