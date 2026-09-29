-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sum_div_reduceFst_le_ord_residues
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5b4815d7-7507-5312-83c7-8582fbf80543

import Definitions.Def_ModularCurve_NodeDepth
import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_two_le_ringKrullDim_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_total
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_div_reduceFst_le_ord_residues
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.UVCrossingModel ModularCurve.NodeLocalized

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace NodeBound
namespace NodeIneq

section Scaling

variable {W : Type u} [CommRing W]

private noncomputable def smulNF (w : W) (ab : PowerSeries W × PowerSeries W) : PowerSeries W × PowerSeries W :=
  (PowerSeries.C w * ab.1, PowerSeries.C w * ab.2)

private theorem inU_C_mul (w : W) (p : PowerSeries W) :
    inU (PowerSeries.C w * p) = MvPowerSeries.C w * inU p := by
  ext d
  rw [coeff_inU, MvPowerSeries.coeff_C_mul, coeff_inU]
  split_ifs with h
  · rw [PowerSeries.coeff_C_mul]
  · rw [mul_zero]

private theorem inV_C_mul (w : W) (p : PowerSeries W) :
    inV (PowerSeries.C w * p) = MvPowerSeries.C w * inV p := by
  ext d
  rw [coeff_inV, MvPowerSeries.coeff_C_mul, coeff_inV]
  split_ifs with h
  · rw [PowerSeries.coeff_C_mul]
  · rw [mul_zero]

private theorem inU_add_inV_smulNF (w : W) (ab : PowerSeries W × PowerSeries W) :
    inU (smulNF w ab).1 + inV (smulNF w ab).2 = MvPowerSeries.C w * (inU ab.1 + inV ab.2) := by
  simp only [smulNF]
  rw [inU_C_mul, inV_C_mul, mul_add]

private theorem constantCoeff_smulNF_snd (w : W) (ab : PowerSeries W × PowerSeries W) (h : PowerSeries.constantCoeff ab.2 = 0) :
    PowerSeries.constantCoeff (smulNF w ab).2 = 0 := by
  simp only [smulNF]
  rw [map_mul, h, mul_zero]

private theorem mk_smulNF (π : W) (w : W) (ab : PowerSeries W × PowerSeries W) :
    mk π (inU (smulNF w ab).1 + inV (smulNF w ab).2) = const π w * mk π (inU ab.1 + inV ab.2) := by
  rw [inU_add_inV_smulNF, map_mul]; rfl

private theorem nfCoeff_smulNF (w : W) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    nfCoeff (smulNF w ab) n = w * nfCoeff ab n := by
  cases n with
  | ofNat i => simp only [nfCoeff, smulNF]; rw [PowerSeries.coeff_C_mul]
  | negSucc j => simp only [nfCoeff, smulNF]; rw [PowerSeries.coeff_C_mul]

end Scaling

section DVR

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

private theorem termOrder_smulNF (w : W) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (IsDiscreteValuationRing.addVal W) E t (smulNF w ab) n =
      IsDiscreteValuationRing.addVal W w + termOrder (IsDiscreteValuationRing.addVal W) E t ab n := by
  simp only [termOrder]
  rw [nfCoeff_smulNF, IsDiscreteValuationRing.addVal_mul, add_assoc]

private theorem add_iInf_enat {ι : Type*} [Nonempty ι] (c : ℕ∞) (g : ι → ℕ∞) :
    (⨅ i, (c + g i)) = c + ⨅ i, g i := by
  apply le_antisymm
  · obtain ⟨i₀, hi₀⟩ := ENat.exists_eq_iInf g
    rw [← hi₀]
    exact iInf_le (fun i => c + g i) i₀
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le g i)

private theorem repGaussOrder_C_mul (w : W) (E t : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder (IsDiscreteValuationRing.addVal W) E t (MvPowerSeries.C w * F) =
      IsDiscreteValuationRing.addVal W w + repGaussOrder (IsDiscreteValuationRing.addVal W) E t F := by
  simp only [repGaussOrder]
  rw [← add_iInf_enat]
  refine iInf_congr fun d => ?_
  rw [MvPowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, add_assoc]

private theorem dominantIndices_smulNF (w : W) (hw : w ≠ 0) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (IsDiscreteValuationRing.addVal W) E t (smulNF w ab) =
      dominantIndices (IsDiscreteValuationRing.addVal W) E t ab := by
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq]
  rw [termOrder_smulNF, inU_add_inV_smulNF, repGaussOrder_C_mul]
  have hfin : IsDiscreteValuationRing.addVal W w ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hw
  exact add_right_inj_of_ne_top hfin

end DVR

section Main

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

private theorem sInf_dominantIndices_zero_eq_of_mul_eq_const_mul
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (w₀ : W) (hw₀ : w₀ ≠ 0)
    (a b a' x' : UVCrossingModel W (ϖ ^ e)) (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hx' : x' ≠ 0)
    (hrel : a * b = const (ϖ ^ e) w₀ * (a' * x'))
    (nfa nfb nfa' nfx' : PowerSeries W × PowerSeries W)
    (hnfa : PowerSeries.constantCoeff nfa.2 = 0 ∧ mk (ϖ ^ e) (inU nfa.1 + inV nfa.2) = a)
    (hnfb : PowerSeries.constantCoeff nfb.2 = 0 ∧ mk (ϖ ^ e) (inU nfb.1 + inV nfb.2) = b)
    (hnfa' : PowerSeries.constantCoeff nfa'.2 = 0 ∧ mk (ϖ ^ e) (inU nfa'.1 + inV nfa'.2) = a')
    (hnfx' : PowerSeries.constantCoeff nfx'.2 = 0 ∧ mk (ϖ ^ e) (inU nfx'.1 + inV nfx'.2) = x') :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nfa) +
        sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nfb) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nfa') +
        sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nfx') := by

  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  obtain ⟨nfax, ⟨hax0, hax⟩, -⟩ := existsUnique_normalForm ϖ e he (a' * x')

  have hab0 : PowerSeries.constantCoeff (smulNF w₀ nfax).2 = 0 := constantCoeff_smulNF_snd w₀ nfax hax0
  have hab : mk (ϖ ^ e) (inU (smulNF w₀ nfax).1 + inV (smulNF w₀ nfax).2) = a * b := by
    rw [mk_smulNF, hax, hrel]

  obtain ⟨h1, -⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he a ha nfa hnfa.1 hnfa.2
    b hb nfb hnfb.1 hnfb.2 (smulNF w₀ nfax) hab0 hab
  obtain ⟨h2, -⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he a' ha' nfa' hnfa'.1 hnfa'.2
    x' hx' nfx' hnfx'.1 hnfx'.2 nfax hax0 hax
  rw [dominantIndices_smulNF w₀ hw₀] at h1
  rw [← h1, h2]

private theorem sSup_dominantIndices_eq_of_mul_eq_const_mul
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (w₀ : W) (hw₀ : w₀ ≠ 0)
    (a b a' x' : UVCrossingModel W (ϖ ^ e)) (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hx' : x' ≠ 0)
    (hrel : a * b = const (ϖ ^ e) w₀ * (a' * x'))
    (nfa nfb nfa' nfx' : PowerSeries W × PowerSeries W)
    (hnfa : PowerSeries.constantCoeff nfa.2 = 0 ∧ mk (ϖ ^ e) (inU nfa.1 + inV nfa.2) = a)
    (hnfb : PowerSeries.constantCoeff nfb.2 = 0 ∧ mk (ϖ ^ e) (inU nfb.1 + inV nfb.2) = b)
    (hnfa' : PowerSeries.constantCoeff nfa'.2 = 0 ∧ mk (ϖ ^ e) (inU nfa'.1 + inV nfa'.2) = a')
    (hnfx' : PowerSeries.constantCoeff nfx'.2 = 0 ∧ mk (ϖ ^ e) (inU nfx'.1 + inV nfx'.2) = x') :
    sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nfa) +
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nfb) =
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nfa') +
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nfx') := by
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  obtain ⟨nfax, ⟨hax0, hax⟩, -⟩ := existsUnique_normalForm ϖ e he (a' * x')
  have hab0 : PowerSeries.constantCoeff (smulNF w₀ nfax).2 = 0 := constantCoeff_smulNF_snd w₀ nfax hax0
  have hab : mk (ϖ ^ e) (inU (smulNF w₀ nfax).1 + inV (smulNF w₀ nfax).2) = a * b := by
    rw [mk_smulNF, hax, hrel]
  obtain ⟨-, h1⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he a ha nfa hnfa.1 hnfa.2
    b hb nfb hnfb.1 hnfb.2 (smulNF w₀ nfax) hab0 hab
  obtain ⟨-, h2⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he a' ha' nfa' hnfa'.1 hnfa'.2
    x' hx' nfx' hnfx'.1 hnfx'.2 nfax hax0 hax
  rw [dominantIndices_smulNF w₀ hw₀] at h1
  rw [← h1, h2]

private theorem dominantIndices_eq_of_mk_eq_const_mul
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (t : ℕ)
    (w₀ : W) (hw₀ : w₀ ≠ 0) (y : UVCrossingModel W (ϖ ^ e))
    (nfy : PowerSeries W × PowerSeries W)
    (hnfy : PowerSeries.constantCoeff nfy.2 = 0 ∧ mk (ϖ ^ e) (inU nfy.1 + inV nfy.2) = y)
    (nfc : PowerSeries W × PowerSeries W)
    (hnfc : PowerSeries.constantCoeff nfc.2 = 0 ∧ mk (ϖ ^ e) (inU nfc.1 + inV nfc.2) = const (ϖ ^ e) w₀ * y) :
    dominantIndices (IsDiscreteValuationRing.addVal W) e t nfc =
      dominantIndices (IsDiscreteValuationRing.addVal W) e t nfy := by
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)

  have h1 : PowerSeries.constantCoeff (smulNF w₀ nfy).2 = 0 ∧ mk (ϖ ^ e) (inU (smulNF w₀ nfy).1 + inV (smulNF w₀ nfy).2) = const (ϖ ^ e) w₀ * y :=
    ⟨constantCoeff_smulNF_snd w₀ nfy hnfy.1, by rw [mk_smulNF, hnfy.2]⟩
  have heq : nfc = smulNF w₀ nfy := (existsUnique_normalForm ϖ e he (const (ϖ ^ e) w₀ * y)).unique hnfc h1
  rw [heq, dominantIndices_smulNF w₀ hw₀]

end Main

end NodeBound.NodeIneq

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace NodeBound
namespace NodeIneq

section Readings

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

private theorem one_mul_addVal :
    (fun w : W => (1 : ℕ∞) * IsDiscreteValuationRing.addVal W w) = (IsDiscreteValuationRing.addVal W : W → ℕ∞) := by
  funext w; exact one_mul _

private theorem finsum_rank_mul_length_eq_of_sInf_eq_of_sSup_eq
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (nf : PowerSeries W × PowerSeries W)
    (hnf : PowerSeries.constantCoeff nf.2 = 0 ∧ mk (ϖ ^ e) (inU nf.1 + inV nf.2) = x)
    (s t : ℤ) (hs : sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nf) = s)
    (ht : sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nf) = t) :
    (∑ᶠ (P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (_ : P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal),
      (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ P.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime P.asIdeal)
              (LocalizedModule P.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))) =
      ((s - t).toNat : ℕ∞) := by
  have h := finsum_rank_mul_length_eq_sInf_sub_sSup ϖ hϖ e he 1 le_rfl x hx nf hnf.1 hnf.2
  simp only [Nat.cast_one, one_mul] at h
  rw [← hs, ← ht]
  exact h

private theorem sInf_dominantIndices_zero_eq_of_sub_mul_U_pow_mem'
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (nf : PowerSeries W × PowerSeries W)
    (hnf : PowerSeries.constantCoeff nf.2 = 0 ∧ mk (ϖ ^ e) (inU nf.1 + inV nf.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
    (h : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}) :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 nf) = (m : ℤ) := by
  have h' := (sInf_dominantIndices_eq_of_sub_mul_U_pow_mem ϖ hϖ e he 1 le_rfl x hx nf hnf.1 hnf.2 γ hγ m h).2
  simp only [Nat.cast_one, one_mul] at h'
  exact h'

private theorem sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem'
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (nf : PowerSeries W × PowerSeries W)
    (hnf : PowerSeries.constantCoeff nf.2 = 0 ∧ mk (ϖ ^ e) (inU nf.1 + inV nf.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (n : ℕ)
    (h : x - γ * V (ϖ ^ e) ^ n ∈ Ideal.span {const (ϖ ^ e) ϖ, U (ϖ ^ e)}) :
    sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e nf) = -(n : ℤ) := by
  have h' := (sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem ϖ hϖ e he 1 le_rfl x hx nf hnf.1 hnf.2 γ hγ n h).2
  simp only [Nat.cast_one, one_mul] at h'
  exact h'

end Readings

end NodeBound.NodeIneq

namespace NodeBound
namespace NodeIneqShape

open Finset

variable {α β : Type*}

private theorem eq_support_filter [DecidableEq β] (D : α →₀ ℤ) (ordf : α → ℤ) (hD : ∀ a, D a = ordf a)
    (r : α → β) (w : β) (T : Finset α) (hT : ∀ a, a ∈ T ↔ ordf a ≠ 0 ∧ r a = w) :
    T = D.support.filter (fun a => r a = w) := by
  ext a
  rw [hT, mem_filter, Finsupp.mem_support_iff, hD]

private theorem cast_sum_toNat_eq_sum_filter [DecidableEq β] (D : α →₀ ℤ) (ordf : α → ℤ) (hD : ∀ a, D a = ordf a)
    (r : α → β) (w : β) (T : Finset α) (hT : ∀ a, a ∈ T ↔ ordf a ≠ 0 ∧ r a = w)
    (hnn : ∀ a ∈ T, 0 ≤ ordf a) :
    ((∑ a ∈ T, (ordf a).toNat : ℕ) : ℤ) = ∑ a ∈ D.support.filter (fun a => r a = w), D a := by
  rw [← eq_support_filter D ordf hD r w T hT, Nat.cast_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [hD, Int.toNat_of_nonneg (hnn a ha)]

private theorem cast_sum_toNat_eq_cast_toNat_sum_filter [DecidableEq β] (D : α →₀ ℤ) (ordf : α → ℤ) (hD : ∀ a, D a = ordf a)
    (r : α → β) (w : β) (T : Finset α) (hT : ∀ a, a ∈ T ↔ ordf a ≠ 0 ∧ r a = w)
    (hnn : ∀ a ∈ T, 0 ≤ ordf a) :
    ((∑ a ∈ T, (ordf a).toNat : ℕ) : ℕ∞) = ((∑ a ∈ D.support.filter (fun a => r a = w), D a).toNat : ℕ∞) := by
  have h := cast_sum_toNat_eq_sum_filter D ordf hD r w T hT hnn
  have h0 : 0 ≤ ∑ a ∈ D.support.filter (fun a => r a = w), D a := by rw [← h]; exact Int.natCast_nonneg _
  congr 1
  apply Int.ofNat.inj
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, h, Int.toNat_of_nonneg h0]

private theorem sum_filter_eq_cast_sum_toNat [DecidableEq β] (D : α →₀ ℤ) (ordf : α → ℤ) (hD : ∀ a, D a = ordf a)
    (r : α → β) (w : β) (T : Finset α) (hT : ∀ a, a ∈ T ↔ ordf a ≠ 0 ∧ r a = w)
    (hnn : ∀ a ∈ T, 0 ≤ ordf a) :
    ∑ a ∈ D.support.filter (fun a => r a = w), D a = ((∑ a ∈ T, (ordf a).toNat : ℕ) : ℤ) :=
  (cast_sum_toNat_eq_sum_filter D ordf hD r w T hT hnn).symm

private theorem natCast_le_natCast_iff_enat (m n : ℕ) : ((m : ℕ∞) ≤ (n : ℕ∞)) ↔ m ≤ n := Nat.cast_le

end NodeBound.NodeIneqShape

namespace NodeBound
namespace NodeIneq

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.UVCrossingModel ModularCurve.NodeLocalized

open Classical in

private theorem sum_div_le_of_finsum_le
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (z : ↥(R.nodeIntegersOver K w)) (hz : z ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ V, D V = V.ord (z : ↥(modularFunctionFieldBar (N * q))))
    (M : ℕ)
    (hM : (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ z)}))) ≤ (M : ℕ∞)) :
    (∑ V ∈ D.support with P.reduceFst V = w, D V) ≤ (M : ℤ) := by
  set T := D.support.filter (fun V => P.reduceFst V = w) with hTdef
  have hTtot : ∀ V, V ∈ T ↔ (V.ord ((z : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w) := fun V => by
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hD]
  have hP2 := ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_le_finsum_rank_mul_length_total
    R K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx z hz T hTtot
  have h1 : ((∑ V ∈ T, (V.ord ((z : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤ (M : ℕ∞) := hP2.trans hM
  have h2 : (∑ V ∈ T, (V.ord ((z : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) ≤ M := by exact_mod_cast h1
  have hnn : ∀ V ∈ T, 0 ≤ V.ord ((z : ↥(modularFunctionFieldBar (N * q)))) := fun V hV =>
    R.ord_nonneg_of_mem_nodeIntegers z.2.1 ((hTtot V).mp hV).2
  have h3 := NodeBound.NodeIneqShape.sum_filter_eq_cast_sum_toNat D (fun V => V.ord ((z : ↥(modularFunctionFieldBar (N * q)))))
    hD P.reduceFst w T hTtot hnn
  have h4 : (∑ V ∈ D.support with P.reduceFst V = w, D V) = ((∑ V ∈ T, (V.ord ((z : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℤ) := by
    convert h3 using 2
  rw [h4]; exact_mod_cast h2

open Classical in

private theorem sum_div_eq_of_finsum_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    [IsAlgClosed k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hιord₁ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hιord₂ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (z : ↥(R.nodeIntegersOver K w))
    (h₁ : R.nodeResidue₁ w ⟨(z : ↥(modularFunctionFieldBar (N * q))), z.2.1⟩ ≠ 0)
    (h₂ : R.nodeResidue₂ w ⟨(z : ↥(modularFunctionFieldBar (N * q))), z.2.1⟩ ≠ 0)
    (ha : 0 ≤ w.ord (R.nodeResidue₁ w ⟨(z : ↥(modularFunctionFieldBar (N * q))), z.2.1⟩))
    (hb : 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(z : ↥(modularFunctionFieldBar (N * q))), z.2.1⟩))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ V, D V = V.ord (z : ↥(modularFunctionFieldBar (N * q))))
    (M : ℕ)
    (hM : (∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ z)}))) = (M : ℕ∞)) :
    (∑ V ∈ D.support with P.reduceFst V = w, D V) = (M : ℤ) := by
  set T := D.support.filter (fun V => P.reduceFst V = w) with hTdef
  have hTtot : ∀ V, V ∈ T ↔ (V.ord ((z : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w) := fun V => by
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hD]
  have hP2 := ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
    R K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx z hqN hO h₁ h₂ hιord₁ hιord₂ ha hb T hTtot
  have h1 : ((∑ V ∈ T, (V.ord ((z : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) = (M : ℕ∞) := hP2.trans hM
  have h2 : (∑ V ∈ T, (V.ord ((z : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) = M := by exact_mod_cast h1
  have hnn : ∀ V ∈ T, 0 ≤ V.ord ((z : ↥(modularFunctionFieldBar (N * q)))) := fun V hV =>
    R.ord_nonneg_of_mem_nodeIntegers z.2.1 ((hTtot V).mp hV).2
  have h3 := NodeBound.NodeIneqShape.sum_filter_eq_cast_sum_toNat D (fun V => V.ord ((z : ↥(modularFunctionFieldBar (N * q)))))
    hD P.reduceFst w T hTtot hnn
  have h4 : (∑ V ∈ D.support with P.reduceFst V = w, D V) = ((∑ V ∈ T, (V.ord ((z : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℤ) := by
    convert h3 using 2
  rw [h4, h2]

end NodeBound.NodeIneq

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace NodeBound
namespace NodeIneq

section Mono

variable {W : Type u} [CommRing W]

private theorem annulusWeight_zero_nfExponent (E : ℕ) (n : ℤ) :
    annulusWeight E 0 (nfExponent n) = (-n).toNat * E := by
  cases n with
  | ofNat i => simp [annulusWeight, nfExponent]
  | negSucc j =>
      simp only [annulusWeight, nfExponent, Finsupp.single_apply]
      simp

private theorem annulusWeight_self_nfExponent (E : ℕ) (n : ℤ) :
    annulusWeight E E (nfExponent n) = n.toNat * E := by
  cases n with
  | ofNat i => simp [annulusWeight, nfExponent]
  | negSucc j => simp [annulusWeight, nfExponent]

private theorem termOrder_zero_eq (v : W → ℕ∞) (E : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E 0 ab n = v (nfCoeff ab n) + (((-n).toNat * E : ℕ) : ℕ∞) := by
  rw [termOrder, annulusWeight_zero_nfExponent]

private theorem termOrder_self_eq (v : W → ℕ∞) (E : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E E ab n = v (nfCoeff ab n) + ((n.toNat * E : ℕ) : ℕ∞) := by
  rw [termOrder, annulusWeight_self_nfExponent]

private theorem eq_zero_of_forall_nfCoeff_eq_zero (ab : PowerSeries W × PowerSeries W)
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

private theorem iInf_termOrder_ne_top (π : W) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
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

private theorem dominantIndices_nonempty (π : W) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) :
    (dominantIndices (IsDiscreteValuationRing.addVal W) E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ENat.exists_eq_iInf (fun n : ℤ => termOrder (IsDiscreteValuationRing.addVal W) E t ab n)
  refine ⟨n, ?_⟩
  show termOrder _ E t ab n = repGaussOrder _ E t (inU ab.1 + inV ab.2)
  rw [repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E t ab hb]
  exact hn

private theorem repGaussOrder_le_termOrder (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    repGaussOrder (IsDiscreteValuationRing.addVal W) E t (inU ab.1 + inV ab.2) ≤
      termOrder (IsDiscreteValuationRing.addVal W) E t ab n := by
  rw [repGaussOrder_normalForm_eq_iInf_termOrder _ (IsDiscreteValuationRing.addVal_zero) E t ab hb]
  exact iInf_le _ n

private theorem le_of_mem_dominantIndices (π : W) (E : ℕ) (hE : 1 ≤ E) (ab : PowerSeries W × PowerSeries W)
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

private theorem sSup_dominantIndices_le_sInf_dominantIndices [IsAdicComplete (maximalIdeal W) W]
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

end NodeBound.NodeIneq

namespace NodeBound
namespace NodeIneq

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

private theorem isUnit_coeffSubring_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (d : ↥(coeffSubring A K)) :
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

private theorem irreducible_of_redRestrict (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
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

private def enlargeCoordinates (R : ProlongationTuple P) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x.1, hBB' c.x.2⟩
  y := ⟨c.y.1, hBB' c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

private theorem exists_commonUnit_mul_eq (R : ProlongationTuple P)
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (w : Place k (modularFunctionFieldC k N)) (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (E : ℕ) (hE : 1 ≤ E)
    (u : ↥(R.nodeIntegersOver K' w)) (hu : IsUnit u)
    (hxy : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y = (R.nodeConst K' w ϖ : ↥(modularFunctionFieldBar (N * q))) ^ E * u)
    (hmax : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    [IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (hbr : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y}).IsPrime ∧
        Subring.inclusion hBB' c.y ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x} ∧ Subring.inclusion hBB' c.x ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y})
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (g : ↥(modularFunctionFieldBar (N * q))) (hg₁ : g ∈ R.R₁.integers) (hg₂ : g ∈ R.R₂.integers)
    (hgK : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K') :
    ∃ a x' : ↥(R.nodeIntegersOver K' w),
      R.nodeResidue₁ w ⟨x', x'.2.1⟩ ≠ 0 ∧ R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0 ∧ g * (x' : ↥(modularFunctionFieldBar (N * q))) = a := by
  classical
  set c' : R.NodeCoordinates K' w := enlargeCoordinates R hBB' c with hc'
  have hxy' : c'.x * c'.y = R.nodeConst K' w ϖ ^ E * u := Subtype.ext hxy

  obtain ⟨x, y, hx, hy, hy0, hz⟩ := hfrac _ hgK
  have hgy : g * y = x := by
    apply Subtype.ext
    rw [Submonoid.coe_mul]
    exact hz
  have hb0 : (⟨y, hy⟩ : ↥(R.nodeIntegersOver K' w)) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)

  obtain ⟨a₁, b₁, hb₁, hgb₁⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
      R K' w c' ϖ hϖ hmax hbr E hE u hu hxy' ⟨x, hx⟩ ⟨y, hy⟩ hb0 g hg₁ hgy
  obtain ⟨a₂, b₂, hb₂, hgb₂⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
      R K' w c' ϖ hϖ hmax hbr E hE u hu hxy' ⟨x, hx⟩ ⟨y, hy⟩ hb0 g hg₂ hgy

  by_cases h12 : R.nodeResidue₂ w ⟨b₁, b₁.2.1⟩ ≠ 0
  · exact ⟨a₁, b₁, hb₁, h12, hgb₁⟩
  by_cases h21 : R.nodeResidue₁ w ⟨b₂, b₂.2.1⟩ ≠ 0
  · exact ⟨a₂, b₂, h21, hb₂, hgb₂⟩
  push Not at h12 h21
  refine ⟨a₁ + a₂, b₁ + b₂, ?_, ?_, ?_⟩
  · have e : (⟨((b₁ + b₂ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), (b₁ + b₂).2.1⟩ : ↥(R.nodeIntegers w))
        = ⟨b₁, b₁.2.1⟩ + ⟨b₂, b₂.2.1⟩ := rfl
    rw [e, map_add, h21, add_zero]
    exact hb₁
  · have e : (⟨((b₁ + b₂ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), (b₁ + b₂).2.1⟩ : ↥(R.nodeIntegers w))
        = ⟨b₁, b₁.2.1⟩ + ⟨b₂, b₂.2.1⟩ := rfl
    rw [e, map_add, h12, zero_add]
    exact hb₂
  · rw [Subring.coe_add, Subring.coe_add, mul_add, hgb₁, hgb₂]

end NodeBound.NodeIneq

namespace NodeBound
namespace NodeIneq

section Generic
variable {α β : Type*}

private theorem sum_filter_support_eq_sum_filter [DecidableEq β] (X : α →₀ ℤ) (r : α → β) (w : β)
    (S : Finset α) (hS : X.support ⊆ S) :
    (∑ a ∈ X.support with r a = w, X a) = ∑ a ∈ S with r a = w, X a := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hS)
  intro a ha hna
  rw [Finset.mem_filter] at ha
  by_contra h
  exact hna (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, ha.2⟩)

private theorem sum_filter_support_eq_sub [DecidableEq β] (D Dg Dh : α →₀ ℤ) (hD : ∀ a, D a = Dh a - Dg a)
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

end Generic

section Places
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, Place.coe_algebraMap] at h

private theorem sum_div_eq_sum_div_sub_sum_div {β : Type*} [DecidableEq β]
    (f x a : F) (c : K) (hc : c ≠ 0) (hf : f ≠ 0) (hx : x ≠ 0) (hrel : c • f * x = a)
    (D Dx Da : Divisor K F) (hD : ∀ V, D V = V.ord f) (hDx : ∀ V, Dx V = V.ord x) (hDa : ∀ V, Da V = V.ord a)
    (r : Place K F → β) (w : β) :
    (∑ V ∈ D.support with r V = w, D V) =
      (∑ V ∈ Da.support with r V = w, Da V) - ∑ V ∈ Dx.support with r V = w, Dx V := by
  refine sum_filter_support_eq_sub D Dx Da (fun V => ?_) r w
  rw [hD, hDx, hDa, ← hrel, Algebra.smul_def, V.ord_mul (mul_ne_zero ((map_ne_zero _).mpr hc) hf) hx,
    V.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap]
  ring

end Places

end NodeBound.NodeIneq

set_option maxHeartbeats 48000000 in

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

    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K')
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (hc₁ : c₁ ∈ K') (hc₂ : c₂ ∈ K') (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)

    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f) :
    (∑ V ∈ D.support with P.reduceFst V = w, D V) ≤
      w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
  classical

  have hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A := NodeBound.NodeIneq.red_eq_zero_iff R
  haveI hdvr0 : IsDiscreteValuationRing ↥(coeffSubring A K') := isDiscreteValuationRing_coeffSubring red hker K'
  have hϖirr : Irreducible ϖ := NodeBound.NodeIneq.irreducible_of_redRestrict R K' ϖ hϖ
  obtain ⟨hWdom, hWdvr, hWcpl, hπ⟩ := PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖirr
  set π : (PowerSeries ↥(coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) :=
    Ideal.Quotient.mk _ (PowerSeries.C ϖ) with hπdef
  set E : ℕ := ew * eK with hEdef
  have hE : 1 ≤ E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set c' : R.NodeCoordinates K' w := NodeBound.NodeIneq.enlargeCoordinates R hBB' c with hc'
  have hxy' : c'.x * c'.y = R.nodeConst K' w ϖ ^ E * u := Subtype.ext hxy

  obtain ⟨θW, θ, hθWo, hθWX, hθsurj, hθC, hθ0, hθ1⟩ :=
    exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver R K' w c' ϖ hϖ hmax' hres
  have hdim := two_le_ringKrullDim_adicCompletion_nodeIntegersOver R K' w c' ϖ hbr.1 hbr.2.2.1
  have hθπ : θ (MvPowerSeries.C π) = algebraMap _ _ (R.nodeConst K' w ϖ) := by
    rw [show θ (MvPowerSeries.C π) = (θ.comp MvPowerSeries.C) π from rfl, hθC]; exact hθWo ϖ
  obtain ⟨ι, α, β, hαu, hβu, hιconst, hιx, hιy, hιord₁, hιord₂⟩ :=
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

  rcases A.mem_or_inv_mem (c₁ / c₂) with hδA | hδA
  ·
    set g : ↥(modularFunctionFieldBar (N * q)) := c₁ • f with hgdef
    have hg₂ : g ∈ R.R₂.integers := by
      have : g = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₁ / c₂) * (c₂ • f) := by
        rw [hgdef, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ c₁ hc₂0]
      rw [this]
      exact mul_mem ((R.R₂.algebraMap_mem_iff (c₁ / c₂)).mpr hδA) h₂
    have hgK : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K' := by
      rw [hgdef, IntermediateField.coe_smul, Algebra.smul_def]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨⟨c₁, hc₁⟩, rfl⟩)) hfK

    obtain ⟨a, x', hx'₁, hx'₂, hgx'⟩ :=
      NodeBound.NodeIneq.exists_commonUnit_mul_eq R w hBB' ϖ hϖ c E hE u hu hxy hmax hbr hfrac g h₁ hg₂ hgK

    have hg'K : ((c₂ • f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K' := by
      rw [IntermediateField.coe_smul, Algebra.smul_def]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨⟨c₂, hc₂⟩, rfl⟩)) hfK
    obtain ⟨xx, yy, hxx, hyy, hyy0, hzz⟩ := hfrac _ hg'K
    have hzzF : (c₂ • f) * yy = xx := by
      apply Subtype.ext; rw [MulMemClass.coe_mul]; exact hzz
    obtain ⟨a₂, b₂, hb₂, hgb₂⟩ :=
      exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero R K' w c' ϖ hϖ hmax hbr E hE u hu hxy' ⟨xx, hxx⟩ ⟨yy, hyy⟩
        (fun h => hyy0 (congrArg Subtype.val h)) (c₂ • f) h₂ hzzF

    have hc₁F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ ≠ 0 := (map_ne_zero _).mpr hc₁0
    have hc₂F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ ≠ 0 := (map_ne_zero _).mpr hc₂0
    have hg0 : g ≠ 0 := by rw [hgdef, Algebra.smul_def]; exact mul_ne_zero hc₁F hf
    have hx'0 : x' ≠ 0 := by
      intro h0; apply hx'₁
      have e : (⟨((x' : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
        Subtype.ext (by rw [h0]; rfl)
      rw [e, map_zero]
    have hb₂0 : b₂ ≠ 0 := by
      intro h0; apply hb₂
      have e : (⟨((b₂ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
        Subtype.ext (by rw [h0]; rfl)
      rw [e, map_zero]
    have ha0 : a ≠ 0 := by
      intro h0
      have : g * (x' : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hgx', h0]; rfl
      rcases mul_eq_zero.mp this with h | h
      · exact hg0 h
      · exact hx'0 (Subtype.ext h)
    have ha₂0 : a₂ ≠ 0 := by
      intro h0
      have : (c₂ • f) * (b₂ : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hgb₂, h0]; rfl
      rcases mul_eq_zero.mp this with h | h
      · rw [Algebra.smul_def] at h; exact (mul_ne_zero hc₂F hf) h
      · exact hb₂0 (Subtype.ext h)

    obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ↥(coeffSubring A K'), δ₀ = ⟨c₁ / c₂, hδA, (div_mem hc₁ hc₂ : c₁ / c₂ ∈ K')⟩ := ⟨_, rfl⟩
    have hidB : a * b₂ = R.nodeConst K' w δ₀ * (a₂ * x') := by
      apply Subtype.ext
      show (a : ↥(modularFunctionFieldBar (N * q))) * b₂ = (R.nodeConst K' w δ₀ : ↥(modularFunctionFieldBar (N * q))) * (a₂ * x')
      rw [ProlongationTuple.coe_nodeConst, hδ₀, ← hgx', ← hgb₂, hgdef, Algebra.smul_def, Algebra.smul_def]
      show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ * f * ↑x' * ↑b₂ =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₁ / c₂) * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ * f * ↑b₂ * ↑x')
      rw [map_div₀]
      field_simp
    obtain ⟨A₁, hA₁⟩ : ∃ z, z = ι (algebraMap _ _ a) := ⟨_, rfl⟩
    obtain ⟨X₁, hX₁⟩ : ∃ z, z = ι (algebraMap _ _ x') := ⟨_, rfl⟩
    obtain ⟨A₂, hA₂⟩ : ∃ z, z = ι (algebraMap _ _ a₂) := ⟨_, rfl⟩
    obtain ⟨B₂, hB₂⟩ : ∃ z, z = ι (algebraMap _ _ b₂) := ⟨_, rfl⟩
    have hA₁0 : A₁ ≠ 0 := hA₁ ▸ hιne a ha0
    have hX₁0 : X₁ ≠ 0 := hX₁ ▸ hιne x' hx'0
    have hA₂0 : A₂ ≠ 0 := hA₂ ▸ hιne a₂ ha₂0
    have hB₂0 : B₂ ≠ 0 := hB₂ ▸ hιne b₂ hb₂0
    obtain ⟨w₀, hw₀def⟩ : ∃ z, z = Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C δ₀) := ⟨_, rfl⟩
    have hidM : A₁ * B₂ = const (π ^ E) w₀ * (A₂ * X₁) := by
      have := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => ι (algebraMap _ _ z)) hidB
      simp only [map_mul] at this
      rw [hιo δ₀] at this
      rw [hA₁, hB₂, hA₂, hX₁, hw₀def]
      exact this
    have hw₀ : w₀ ≠ 0 := by
      intro h0
      have h1 : ι (algebraMap _ _ (R.nodeConst K' w δ₀)) = 0 := by
        rw [hιo δ₀, ← hw₀def, h0]
        exact map_zero (constHom (π ^ E))
      have h2 : R.nodeConst K' w δ₀ ≠ 0 := by
        intro h
        have h' := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => (z : ↥(modularFunctionFieldBar (N * q)))) h
        simp only [ProlongationTuple.coe_nodeConst, ZeroMemClass.coe_zero, map_eq_zero] at h'
        rw [hδ₀] at h'
        rcases div_eq_zero_iff.mp h' with h'' | h''
        · exact hc₁0 h''
        · exact hc₂0 h''
      exact hιne _ h2 h1

    obtain ⟨nfa, hnfa, -⟩ := existsUnique_normalForm π E hE A₁
    obtain ⟨nfx, hnfx, -⟩ := existsUnique_normalForm π E hE X₁
    obtain ⟨nfa₂, hnfa₂, -⟩ := existsUnique_normalForm π E hE A₂
    obtain ⟨nfb₂, hnfb₂, -⟩ := existsUnique_normalForm π E hE B₂

    obtain ⟨n₁, hn₁⟩ : ∃ z : ℤ, z = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := ⟨_, rfl⟩
    obtain ⟨n₂, hn₂⟩ : ∃ z : ℤ, z = (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := ⟨_, rfl⟩
    obtain ⟨m₁, hm₁⟩ : ∃ z : ℤ, z = w.ord (R.nodeResidue₁ w ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ : ↥(modularFunctionFieldC k N)) := ⟨_, rfl⟩
    obtain ⟨m₂, hm₂⟩ : ∃ z : ℤ, z = (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ : ↥(modularFunctionFieldC k N)) := ⟨_, rfl⟩
    obtain ⟨k₂, hk₂⟩ : ∃ z : ℤ, z = (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(modularFunctionFieldC k N)) := ⟨_, rfl⟩
    have hm₁0 : 0 ≤ m₁ := hm₁ ▸ (hregB x').1
    have hm₂0 : 0 ≤ m₂ := hm₂ ▸ (hregB x').2
    have hk₂0 : 0 ≤ k₂ := hk₂ ▸ (hregB b₂).2

    have hres₁a : (R.nodeResidue₁ w ⟨(a : ↥(modularFunctionFieldBar (N * q))), a.2.1⟩ : ↥(modularFunctionFieldC k N))
        = R.residue₁ ⟨c₁ • f, h₁⟩ * R.nodeResidue₁ w ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ := by
      rw [nodeResidue₁_apply, nodeResidue₁_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgx'.symm
    have hres₂a₂ : (R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N))
        = R.residue₂ ⟨c₂ • f, h₂⟩ * R.nodeResidue₂ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ := by
      rw [nodeResidue₂_apply, nodeResidue₂_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgb₂.symm
    have hu₁' : (R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
      intro h0; apply hu₁; rwa [ProlongationTuple.residue₁_apply, map_eq_zero_iff _ R.ι.injective] at h0
    have hu₂' : (R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
      intro h0; apply hu₂; rwa [ProlongationTuple.residue₂_apply, map_eq_zero_iff _ R.ι.injective] at h0
    have ha₁ne : R.nodeResidue₁ w ⟨(a : ↥(modularFunctionFieldBar (N * q))), a.2.1⟩ ≠ 0 := by
      rw [hres₁a]; exact mul_ne_zero hu₁' hx'₁
    have ha₂ne : R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ ≠ 0 := by
      rw [hres₂a₂]; exact mul_ne_zero hu₂' hb₂
    have horda : w.ord (R.nodeResidue₁ w ⟨(a : ↥(modularFunctionFieldBar (N * q))), a.2.1⟩ : ↥(modularFunctionFieldC k N)) = n₁ + m₁ := by
      rw [hres₁a, w.ord_mul hu₁' hx'₁, hn₁, hm₁]
    have horda₂ : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N)) = n₂ + k₂ := by
      rw [hres₂a₂, (arithFrobC q k N • w).ord_mul hu₂' hb₂, hn₂, hk₂]
    have hN₁0 : 0 ≤ n₁ + m₁ := horda ▸ (hregB a).1
    have hN₂0 : 0 ≤ n₂ + k₂ := horda₂ ▸ (hregB a₂).2

    obtain ⟨γ₁, hγ₁, hr₁⟩ := hιord₁ x' m₁.toNat hx'₁ (by rw [Int.toNat_of_nonneg hm₁0, hm₁])
    obtain ⟨γ₂, hγ₂, hr₂⟩ := hιord₂ x' m₂.toNat hx'₂ (by rw [Int.toNat_of_nonneg hm₂0, hm₂])
    obtain ⟨γ₃, hγ₃, hr₃⟩ := hιord₁ a (n₁ + m₁).toNat ha₁ne (by rw [Int.toNat_of_nonneg hN₁0]; exact horda)
    obtain ⟨γ₄, hγ₄, hr₄⟩ := hιord₂ b₂ k₂.toNat hb₂ (by rw [Int.toNat_of_nonneg hk₂0, hk₂])
    obtain ⟨γ₅, hγ₅, hr₅⟩ := hιord₂ a₂ (n₂ + k₂).toNat ha₂ne (by rw [Int.toNat_of_nonneg hN₂0]; exact horda₂)
    have hSx : sSup (dominantIndices (IsDiscreteValuationRing.addVal _) E E nfx) = -((m₁.toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem' π hπ E hE X₁ hX₁0 nfx hnfx γ₁ hγ₁ _ (hX₁ ▸ hr₁)
    have hIx : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfx) = ((m₂.toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sInf_dominantIndices_zero_eq_of_sub_mul_U_pow_mem' π hπ E hE X₁ hX₁0 nfx hnfx γ₂ hγ₂ _ (hX₁ ▸ hr₂)
    have hSa : sSup (dominantIndices (IsDiscreteValuationRing.addVal _) E E nfa) = -(((n₁ + m₁).toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem' π hπ E hE A₁ hA₁0 nfa hnfa γ₃ hγ₃ _ (hA₁ ▸ hr₃)
    have hIb₂ : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfb₂) = ((k₂.toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sInf_dominantIndices_zero_eq_of_sub_mul_U_pow_mem' π hπ E hE B₂ hB₂0 nfb₂ hnfb₂ γ₄ hγ₄ _ (hB₂ ▸ hr₄)
    have hIa₂ : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfa₂) = (((n₂ + k₂).toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sInf_dominantIndices_zero_eq_of_sub_mul_U_pow_mem' π hπ E hE A₂ hA₂0 nfa₂ hnfa₂ γ₅ hγ₅ _ (hA₂ ▸ hr₅)

    have hItr := NodeBound.NodeIneq.sInf_dominantIndices_zero_eq_of_mul_eq_const_mul π hπ E hE w₀ hw₀ A₁ B₂ A₂ X₁
      hA₁0 hB₂0 hA₂0 hX₁0 hidM nfa nfb₂ nfa₂ nfx hnfa hnfb₂ hnfa₂ hnfx
    have hIa : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfa) = n₂ + m₂ := by
      rw [hIb₂, hIa₂, hIx, Int.toNat_of_nonneg hk₂0, Int.toNat_of_nonneg hN₂0, Int.toNat_of_nonneg hm₂0] at hItr
      linarith

    have hTa := NodeBound.NodeIneq.finsum_rank_mul_length_eq_of_sInf_eq_of_sSup_eq π hπ E hE A₁ hA₁0 nfa hnfa _ _ hIa hSa
    have hTx := NodeBound.NodeIneq.finsum_rank_mul_length_eq_of_sInf_eq_of_sSup_eq π hπ E hE X₁ hX₁0 nfx hnfx _ _ hIx hSx
    rw [Int.toNat_of_nonneg hN₁0] at hTa
    rw [Int.toNat_of_nonneg hm₁0, Int.toNat_of_nonneg hm₂0] at hTx

    haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
    obtain ⟨Da, hDa, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      ((a : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) (fun h => ha0 (Subtype.ext h))
    obtain ⟨Dx, hDx, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      ((x' : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) (fun h => hx'0 (Subtype.ext h))
    have hLE := NodeBound.NodeIneq.sum_div_le_of_finsum_le R K' w c' ϖ hmax' hres hVI (hW₀ w hw) π hπ E hE ι hιϖ α hαu hιx
      a ha0 Da hDa ((n₂ + m₂ - -(n₁ + m₁)).toNat) (by rw [← hA₁, hTa])
    have hEQ := NodeBound.NodeIneq.sum_div_eq_of_finsum_eq R K' w c' ϖ hmax' hres hVI (hW₀ w hw) π hπ E hE ι hιϖ α hαu hιx
      hqN hO hιord₁ hιord₂ x' hx'₁ hx'₂ (hm₁ ▸ hm₁0) (hm₂ ▸ hm₂0) Dx hDx ((m₂ - -m₁).toNat) (by rw [← hX₁, hTx])
    have hmono := NodeBound.NodeIneq.sSup_dominantIndices_le_sInf_dominantIndices π hπ E hE A₁ hA₁0 nfa hnfa
    rw [hIa, hSa, Int.toNat_of_nonneg hN₁0] at hmono
    rw [Int.toNat_of_nonneg (by linarith)] at hLE
    rw [Int.toNat_of_nonneg (by linarith)] at hEQ

    have hsplit := NodeBound.NodeIneq.sum_div_eq_sum_div_sub_sum_div f
      ((x' : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))
      ((a : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) c₁ hc₁0 hf
      (fun h => hx'0 (Subtype.ext h)) hgx' D Dx Da hDf hDx hDa P.reduceFst w
    rw [hsplit, ← hn₁, ← hn₂]
    linarith
  ·
    rw [inv_div] at hδA
    set g : ↥(modularFunctionFieldBar (N * q)) := c₂ • f with hgdef
    have hg₁ : g ∈ R.R₁.integers := by
      have : g = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₂ / c₁) * (c₁ • f) := by
        rw [hgdef, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ c₂ hc₁0]
      rw [this]
      exact mul_mem ((R.R₁.algebraMap_mem_iff (c₂ / c₁)).mpr hδA) h₁
    have hgK : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K' := by
      rw [hgdef, IntermediateField.coe_smul, Algebra.smul_def]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨⟨c₂, hc₂⟩, rfl⟩)) hfK

    obtain ⟨a, x', hx'₁, hx'₂, hgx'⟩ :=
      NodeBound.NodeIneq.exists_commonUnit_mul_eq R w hBB' ϖ hϖ c E hE u hu hxy hmax hbr hfrac g hg₁ h₂ hgK

    have hg'K : ((c₁ • f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K' := by
      rw [IntermediateField.coe_smul, Algebra.smul_def]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨⟨c₁, hc₁⟩, rfl⟩)) hfK
    obtain ⟨xx, yy, hxx, hyy, hyy0, hzz⟩ := hfrac _ hg'K
    have hzzF : (c₁ • f) * yy = xx := by
      apply Subtype.ext; rw [MulMemClass.coe_mul]; exact hzz
    obtain ⟨a₂, b₂, hb₂, hgb₂⟩ :=
      exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero R K' w c' ϖ hϖ hmax hbr E hE u hu hxy' ⟨xx, hxx⟩ ⟨yy, hyy⟩
        (fun h => hyy0 (congrArg Subtype.val h)) (c₁ • f) h₁ hzzF

    have hc₁F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ ≠ 0 := (map_ne_zero _).mpr hc₁0
    have hc₂F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ ≠ 0 := (map_ne_zero _).mpr hc₂0
    have hg0 : g ≠ 0 := by rw [hgdef, Algebra.smul_def]; exact mul_ne_zero hc₂F hf
    have hx'0 : x' ≠ 0 := by
      intro h0; apply hx'₁
      have e : (⟨((x' : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
        Subtype.ext (by rw [h0]; rfl)
      rw [e, map_zero]
    have hb₂0 : b₂ ≠ 0 := by
      intro h0; apply hb₂
      have e : (⟨((b₂ : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
        Subtype.ext (by rw [h0]; rfl)
      rw [e, map_zero]
    have ha0 : a ≠ 0 := by
      intro h0
      have : g * (x' : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hgx', h0]; rfl
      rcases mul_eq_zero.mp this with h | h
      · exact hg0 h
      · exact hx'0 (Subtype.ext h)
    have ha₂0 : a₂ ≠ 0 := by
      intro h0
      have : (c₁ • f) * (b₂ : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hgb₂, h0]; rfl
      rcases mul_eq_zero.mp this with h | h
      · rw [Algebra.smul_def] at h; exact (mul_ne_zero hc₁F hf) h
      · exact hb₂0 (Subtype.ext h)

    obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ↥(coeffSubring A K'), δ₀ = ⟨c₂ / c₁, hδA, (div_mem hc₂ hc₁ : c₂ / c₁ ∈ K')⟩ := ⟨_, rfl⟩
    have hidB : a * b₂ = R.nodeConst K' w δ₀ * (a₂ * x') := by
      apply Subtype.ext
      show (a : ↥(modularFunctionFieldBar (N * q))) * b₂ = (R.nodeConst K' w δ₀ : ↥(modularFunctionFieldBar (N * q))) * (a₂ * x')
      rw [ProlongationTuple.coe_nodeConst, hδ₀, ← hgx', ← hgb₂, hgdef, Algebra.smul_def, Algebra.smul_def]
      show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ * f * ↑x' * ↑b₂ =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₂ / c₁) * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ * f * ↑b₂ * ↑x')
      rw [map_div₀]
      field_simp
    obtain ⟨A₁, hA₁⟩ : ∃ z, z = ι (algebraMap _ _ a) := ⟨_, rfl⟩
    obtain ⟨X₁, hX₁⟩ : ∃ z, z = ι (algebraMap _ _ x') := ⟨_, rfl⟩
    obtain ⟨A₂, hA₂⟩ : ∃ z, z = ι (algebraMap _ _ a₂) := ⟨_, rfl⟩
    obtain ⟨B₂, hB₂⟩ : ∃ z, z = ι (algebraMap _ _ b₂) := ⟨_, rfl⟩
    have hA₁0 : A₁ ≠ 0 := hA₁ ▸ hιne a ha0
    have hX₁0 : X₁ ≠ 0 := hX₁ ▸ hιne x' hx'0
    have hA₂0 : A₂ ≠ 0 := hA₂ ▸ hιne a₂ ha₂0
    have hB₂0 : B₂ ≠ 0 := hB₂ ▸ hιne b₂ hb₂0
    obtain ⟨w₀, hw₀def⟩ : ∃ z, z = Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C δ₀) := ⟨_, rfl⟩
    have hidM : A₁ * B₂ = const (π ^ E) w₀ * (A₂ * X₁) := by
      have := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => ι (algebraMap _ _ z)) hidB
      simp only [map_mul] at this
      rw [hιo δ₀] at this
      rw [hA₁, hB₂, hA₂, hX₁, hw₀def]
      exact this
    have hw₀ : w₀ ≠ 0 := by
      intro h0
      have h1 : ι (algebraMap _ _ (R.nodeConst K' w δ₀)) = 0 := by
        rw [hιo δ₀, ← hw₀def, h0]
        exact map_zero (constHom (π ^ E))
      have h2 : R.nodeConst K' w δ₀ ≠ 0 := by
        intro h
        have h' := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => (z : ↥(modularFunctionFieldBar (N * q)))) h
        simp only [ProlongationTuple.coe_nodeConst, ZeroMemClass.coe_zero, map_eq_zero] at h'
        rw [hδ₀] at h'
        rcases div_eq_zero_iff.mp h' with h'' | h''
        · exact hc₂0 h''
        · exact hc₁0 h''
      exact hιne _ h2 h1

    obtain ⟨nfa, hnfa, -⟩ := existsUnique_normalForm π E hE A₁
    obtain ⟨nfx, hnfx, -⟩ := existsUnique_normalForm π E hE X₁
    obtain ⟨nfa₂, hnfa₂, -⟩ := existsUnique_normalForm π E hE A₂
    obtain ⟨nfb₂, hnfb₂, -⟩ := existsUnique_normalForm π E hE B₂

    obtain ⟨n₁, hn₁⟩ : ∃ z : ℤ, z = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := ⟨_, rfl⟩
    obtain ⟨n₂, hn₂⟩ : ∃ z : ℤ, z = (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := ⟨_, rfl⟩
    obtain ⟨m₁, hm₁⟩ : ∃ z : ℤ, z = w.ord (R.nodeResidue₁ w ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ : ↥(modularFunctionFieldC k N)) := ⟨_, rfl⟩
    obtain ⟨m₂, hm₂⟩ : ∃ z : ℤ, z = (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ : ↥(modularFunctionFieldC k N)) := ⟨_, rfl⟩
    obtain ⟨k₂, hk₂⟩ : ∃ z : ℤ, z = w.ord (R.nodeResidue₁ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(modularFunctionFieldC k N)) := ⟨_, rfl⟩
    have hm₁0 : 0 ≤ m₁ := hm₁ ▸ (hregB x').1
    have hm₂0 : 0 ≤ m₂ := hm₂ ▸ (hregB x').2
    have hk₂0 : 0 ≤ k₂ := hk₂ ▸ (hregB b₂).1

    have hres₂a : (R.nodeResidue₂ w ⟨(a : ↥(modularFunctionFieldBar (N * q))), a.2.1⟩ : ↥(modularFunctionFieldC k N))
        = R.residue₂ ⟨c₂ • f, h₂⟩ * R.nodeResidue₂ w ⟨(x' : ↥(modularFunctionFieldBar (N * q))), x'.2.1⟩ := by
      rw [nodeResidue₂_apply, nodeResidue₂_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgx'.symm
    have hres₁a₂ : (R.nodeResidue₁ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N))
        = R.residue₁ ⟨c₁ • f, h₁⟩ * R.nodeResidue₁ w ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ := by
      rw [nodeResidue₁_apply, nodeResidue₁_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgb₂.symm
    have hu₁' : (R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
      intro h0; apply hu₁; rwa [ProlongationTuple.residue₁_apply, map_eq_zero_iff _ R.ι.injective] at h0
    have hu₂' : (R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
      intro h0; apply hu₂; rwa [ProlongationTuple.residue₂_apply, map_eq_zero_iff _ R.ι.injective] at h0
    have ha₂ne' : R.nodeResidue₂ w ⟨(a : ↥(modularFunctionFieldBar (N * q))), a.2.1⟩ ≠ 0 := by
      rw [hres₂a]; exact mul_ne_zero hu₂' hx'₂
    have ha₁ne' : R.nodeResidue₁ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ ≠ 0 := by
      rw [hres₁a₂]; exact mul_ne_zero hu₁' hb₂
    have horda : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(a : ↥(modularFunctionFieldBar (N * q))), a.2.1⟩ : ↥(modularFunctionFieldC k N)) = n₂ + m₂ := by
      rw [hres₂a, (arithFrobC q k N • w).ord_mul hu₂' hx'₂, hn₂, hm₂]
    have horda₂ : w.ord (R.nodeResidue₁ w ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1⟩ : ↥(modularFunctionFieldC k N)) = n₁ + k₂ := by
      rw [hres₁a₂, w.ord_mul hu₁' hb₂, hn₁, hk₂]
    have hN₂0 : 0 ≤ n₂ + m₂ := horda ▸ (hregB a).2
    have hN₁0 : 0 ≤ n₁ + k₂ := horda₂ ▸ (hregB a₂).1

    obtain ⟨γ₁, hγ₁, hr₁⟩ := hιord₁ x' m₁.toNat hx'₁ (by rw [Int.toNat_of_nonneg hm₁0, hm₁])
    obtain ⟨γ₂, hγ₂, hr₂⟩ := hιord₂ x' m₂.toNat hx'₂ (by rw [Int.toNat_of_nonneg hm₂0, hm₂])
    obtain ⟨γ₃, hγ₃, hr₃⟩ := hιord₂ a (n₂ + m₂).toNat ha₂ne' (by rw [Int.toNat_of_nonneg hN₂0]; exact horda)
    obtain ⟨γ₄, hγ₄, hr₄⟩ := hιord₁ b₂ k₂.toNat hb₂ (by rw [Int.toNat_of_nonneg hk₂0, hk₂])
    obtain ⟨γ₅, hγ₅, hr₅⟩ := hιord₁ a₂ (n₁ + k₂).toNat ha₁ne' (by rw [Int.toNat_of_nonneg hN₁0]; exact horda₂)
    have hSx : sSup (dominantIndices (IsDiscreteValuationRing.addVal _) E E nfx) = -((m₁.toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem' π hπ E hE X₁ hX₁0 nfx hnfx γ₁ hγ₁ _ (hX₁ ▸ hr₁)
    have hIx : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfx) = ((m₂.toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sInf_dominantIndices_zero_eq_of_sub_mul_U_pow_mem' π hπ E hE X₁ hX₁0 nfx hnfx γ₂ hγ₂ _ (hX₁ ▸ hr₂)
    have hIa : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfa) = (((n₂ + m₂).toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sInf_dominantIndices_zero_eq_of_sub_mul_U_pow_mem' π hπ E hE A₁ hA₁0 nfa hnfa γ₃ hγ₃ _ (hA₁ ▸ hr₃)
    have hSb₂ : sSup (dominantIndices (IsDiscreteValuationRing.addVal _) E E nfb₂) = -((k₂.toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem' π hπ E hE B₂ hB₂0 nfb₂ hnfb₂ γ₄ hγ₄ _ (hB₂ ▸ hr₄)
    have hSa₂ : sSup (dominantIndices (IsDiscreteValuationRing.addVal _) E E nfa₂) = -(((n₁ + k₂).toNat : ℕ) : ℤ) :=
      NodeBound.NodeIneq.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem' π hπ E hE A₂ hA₂0 nfa₂ hnfa₂ γ₅ hγ₅ _ (hA₂ ▸ hr₅)

    have hStr := NodeBound.NodeIneq.sSup_dominantIndices_eq_of_mul_eq_const_mul π hπ E hE w₀ hw₀ A₁ B₂ A₂ X₁
      hA₁0 hB₂0 hA₂0 hX₁0 hidM nfa nfb₂ nfa₂ nfx hnfa hnfb₂ hnfa₂ hnfx
    have hSa : sSup (dominantIndices (IsDiscreteValuationRing.addVal _) E E nfa) = -(n₁ + m₁) := by
      rw [hSb₂, hSa₂, hSx, Int.toNat_of_nonneg hk₂0, Int.toNat_of_nonneg hN₁0, Int.toNat_of_nonneg hm₁0] at hStr
      linarith
    have hIa' : sInf (dominantIndices (IsDiscreteValuationRing.addVal _) E 0 nfa) = n₂ + m₂ := by
      rw [hIa, Int.toNat_of_nonneg hN₂0]

    have hst := NodeBound.NodeIneq.sSup_dominantIndices_le_sInf_dominantIndices π hπ E hE A₁ hA₁0 nfa hnfa
    rw [hIa', hSa] at hst

    have hTa := NodeBound.NodeIneq.finsum_rank_mul_length_eq_of_sInf_eq_of_sSup_eq π hπ E hE A₁ hA₁0 nfa hnfa _ _ hIa' hSa
    have hTx := NodeBound.NodeIneq.finsum_rank_mul_length_eq_of_sInf_eq_of_sSup_eq π hπ E hE X₁ hX₁0 nfx hnfx _ _ hIx hSx
    rw [Int.toNat_of_nonneg hm₁0, Int.toNat_of_nonneg hm₂0] at hTx

    haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
    obtain ⟨Da, hDa, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      ((a : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) (fun h => ha0 (Subtype.ext h))
    obtain ⟨Dx, hDx, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      ((x' : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) (fun h => hx'0 (Subtype.ext h))
    have hLE := NodeBound.NodeIneq.sum_div_le_of_finsum_le R K' w c' ϖ hmax' hres hVI (hW₀ w hw) π hπ E hE ι hιϖ α hαu hιx
      a ha0 Da hDa ((n₂ + m₂ - -(n₁ + m₁)).toNat) (by rw [← hA₁, hTa])
    have hEQ := NodeBound.NodeIneq.sum_div_eq_of_finsum_eq R K' w c' ϖ hmax' hres hVI (hW₀ w hw) π hπ E hE ι hιϖ α hαu hιx
      hqN hO hιord₁ hιord₂ x' hx'₁ hx'₂ (hm₁ ▸ hm₁0) (hm₂ ▸ hm₂0) Dx hDx ((m₂ - -m₁).toNat) (by rw [← hX₁, hTx])
    rw [Int.toNat_of_nonneg (by linarith)] at hLE
    rw [Int.toNat_of_nonneg (by linarith)] at hEQ

    have hsplit := NodeBound.NodeIneq.sum_div_eq_sum_div_sub_sum_div f
      ((x' : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q)))
      ((a : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))) c₂ hc₂0 hf
      (fun h => hx'0 (Subtype.ext h)) hgx' D Dx Da hDf hDx hDa P.reduceFst w
    rw [hsplit, ← hn₁, ← hn₂]
    linarith

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_div_reduceFst_le_ord_residues
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_div_reduceFst_le_ord_residues (solution)
