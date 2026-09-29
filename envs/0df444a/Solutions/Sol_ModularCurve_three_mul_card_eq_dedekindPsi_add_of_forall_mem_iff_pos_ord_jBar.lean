-- Prove2me | solution 1 for ModularCurve.three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e0b55bcb-98c7-5475-8be0-1503fb26b9d5

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_jBar_dvd_three_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"

set_option Elab.async false

open ModularCurve AlgebraicCurve

namespace SolH4Private

private lemma eq_one_or_three_of_pos_of_dvd_three {n : ℤ} (hpos : 0 < n) (hdvd : n ∣ 3) :
    n = 1 ∨ n = 3 := by
  have h1 : (1 : ℤ) ≤ n := hpos
  have h3 : n ≤ 3 := Int.le_of_dvd (by norm_num) hdvd
  interval_cases n
  · left; rfl
  · exfalso; rcases hdvd with ⟨k, hk⟩; omega
  · right; rfl

end SolH4Private

theorem solution (N : ℕ) [NeZero N] (hodd : Odd N) (S0 : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) (hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jBar N)) : 3 * S0.card = dedekindPsi N + 2 * (S0.filter fun v => v.ord (jBar N) = 1).card := by

  have hbridge : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 0) =
        v.ord (jBar N) := by
    intro v; simp

  have hsum : ∑ v ∈ S0, v.ord (jBar N) = (dedekindPsi N : ℤ) := by
    have := ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi N 0
      (ModularCurve.deg_eq_one_modularFunctionFieldBar N) S0 ?_
    · simpa [hbridge] using this
    · intro v; rw [hbridge]; exact hS0 v

  have hdich : ∀ v ∈ S0, v.ord (jBar N) = 1 ∨ v.ord (jBar N) = 3 := by
    intro v hv
    have hpos : 0 < v.ord (jBar N) := (hS0 v).mp hv
    have hdvd : v.ord (jBar N) ∣ 3 :=
      ModularCurve.ord_jBar_dvd_three_of_odd N hodd v hpos
    exact SolH4Private.eq_one_or_three_of_pos_of_dvd_three hpos hdvd
  classical

  have hsplit : ∑ v ∈ S0, v.ord (jBar N) =
      ∑ v ∈ S0.filter (fun v => v.ord (jBar N) = 1), v.ord (jBar N) +
      ∑ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1), v.ord (jBar N) :=
    (Finset.sum_filter_add_sum_filter_not S0 _ _).symm

  have hfilter1 : ∑ v ∈ S0.filter (fun v => v.ord (jBar N) = 1), v.ord (jBar N) =
      ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
    rw [Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2]
    simp

  have hfilter3 : ∑ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1), v.ord (jBar N) =
      3 * ((S0.filter fun v => ¬ v.ord (jBar N) = 1).card : ℤ) := by
    have hconst : ∀ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1),
        v.ord (jBar N) = 3 := by
      intro v hv
      have hmem := Finset.mem_filter.mp hv
      rcases hdich v hmem.1 with h1 | h3
      · exact absurd h1 hmem.2
      · exact h3
    rw [Finset.sum_congr rfl hconst]
    simp [mul_comm]
  have hcards : (S0.filter fun v => v.ord (jBar N) = 1).card +
      (S0.filter fun v => ¬ v.ord (jBar N) = 1).card = S0.card :=
    Finset.card_filter_add_card_filter_not _

  have hZ : (3 : ℤ) * S0.card =
      (dedekindPsi N : ℤ) + 2 * ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
    have heq := hsum
    rw [hsplit, hfilter1, hfilter3] at heq
    have hc : ((S0.filter fun v => ¬ v.ord (jBar N) = 1).card : ℤ) =
        (S0.card : ℤ) - ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
      have := hcards; zify at this; omega
    rw [hc] at heq; linarith

  have hN : ((3 * S0.card : ℕ) : ℤ) =
      ((dedekindPsi N + 2 * (S0.filter fun v => v.ord (jBar N) = 1).card : ℕ) : ℤ) := by
    push_cast; linarith [hZ]
  exact_mod_cast hN

end S_ModularCurve_three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar
end P2MW
export P2MW.S_ModularCurve_three_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar (solution)
