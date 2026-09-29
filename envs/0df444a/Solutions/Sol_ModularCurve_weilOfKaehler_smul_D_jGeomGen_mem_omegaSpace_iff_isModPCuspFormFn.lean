-- Prove2me | solution 1 for ModularCurve.weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f24c55ea-ed6a-5f39-8c26-54b9d72e5045

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Theorems.Thm_ModularCurve_ordDifferential_D_jGeomGen_sub_weightFloor_eq
import Theorems.Thm_ModularCurve_mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve WithZero

namespace KSIso

theorem thetaL_jqModC_ne_zero (K : Type) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h0
  have h1 : (thetaL K (jqModC K)).coeff (-1) = 0 := by rw [h0]; rfl
  rw [thetaL_apply, ModularCurve.theta_coeff, ModularCurve.coeff_jqModC_neg_one] at h1
  norm_num at h1

end KSIso

open KSIso in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)]
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N))
    (hdj : KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N) ≠ 0)
    (m m' : ℕ) (hm : 1 ≤ m) (hm' : 1 ≤ m') (hmm' : m + m' = (p + 1) / 2)
    (h : ↥(modularFunctionFieldC K N)) (hh : (h : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)))
    (hcov : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), IsAffineGeomPlace K N w ∨ w.ord (jGeomGen K N) < 0)
    (htame : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N),
      w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0)
    (D : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD1 : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N),
      w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D w = weightFloor K N m w - 1)
    (hD0 : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N),
      ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D w = weightFloor K N m w)
    (f : ↥(modularFunctionFieldC K N)) (hf : f ≠ 0) :
    AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N)
        (ω := f • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) (smul_ne_zero hf hdj)
      ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D ↔
    ModularCurve.IsModPCuspFormFn K m' (((f * h : ↥(modularFunctionFieldC K N)) : LaurentSeries K)) := by
  classical
  have hω : f • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N) ≠ 0 := smul_ne_zero hf hdj

  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0]; rfl
    rw [hh] at this
    exact (zpow_ne_zero _ (thetaL_jqModC_ne_zero K)) this
  have hfh : f * h ≠ 0 := mul_ne_zero hf hh0

  obtain ⟨-, hmem, hmax⟩ := hagree hω
  have step1 : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D ↔
      D ≤ canonicalDivisorOf hω :=
    ⟨fun hm => hmax D hm, fun hle => omegaSpace_antitone hle hmem⟩

  obtain ⟨P, hP, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := K) h hh0
  let E' : Divisor K ↥(modularFunctionFieldC K N) := canonicalDivisorOf hdj - D - P

  have hcanω : ∀ w : Place K ↥(modularFunctionFieldC K N), canonicalDivisorOf hω w = w.ord f + canonicalDivisorOf hdj w := by
    intro w
    rw [canonicalDivisorOf_apply, canonicalDivisorOf_apply]
    exact w.ordDifferential_smul hf (w.differentialCoeff_ne_zero hdj)

  have hbcore := ModularCurve.ordDifferential_D_jGeomGen_sub_weightFloor_eq p hp5 N hpN K m m' hmm' h hh
  have hE' : ∀ w : Place K ↥(modularFunctionFieldC K N), E' w = weightFloor K N m' w - (if w.ord (jGeomGen K N) < 0 then 1 else 0) := by
    intro w
    show (canonicalDivisorOf hdj - D - P) w = _
    rw [Finsupp.sub_apply, Finsupp.sub_apply, canonicalDivisorOf_apply, hP w]
    obtain ⟨h1, h2, h3⟩ := hbcore w
    by_cases hcusp : w.ord (jGeomGen K N) < 0
    · rw [if_pos hcusp]
      have hnss : ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) := by
        rintro ⟨hss, -⟩

        have hss' : IsSupersingularPlace p N K w := hss
        have haff : IsAffineGeomPlace K N w := hss'.2.1
        have : (0 : ℤ) ≤ w.ord (jGeomGen K N) := by
          rcases (w.adicValuation_le_one_iff).mp (w.adicValuation_le_one_of_mem haff.1) with h0 | h0
          · rw [h0, Place.ord_zero]
          · exact h0
        omega
      rw [hD0 w hnss]
      have := h3 hcusp (htame w hcusp)
      omega
    · rw [if_neg hcusp]
      have haff : IsAffineGeomPlace K N w := (hcov w).resolve_right hcusp
      by_cases hss : (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
      · rw [hD1 w hss.1 hss.2]
        have := h1 hss.1 hss.2
        omega
      · rw [hD0 w hss]
        have := h2 haff hss
        omega

  have step4 : D ≤ canonicalDivisorOf hω ↔ (f * h) ∈ AlgebraicCurve.riemannRochSpace (K := K) E' := by
    rw [mem_riemannRochSpace_iff, Finsupp.le_def]
    constructor
    · intro hle w
      right
      show -((canonicalDivisorOf hdj - D - P) w) ≤ w.ord (f * h)
      rw [Finsupp.sub_apply, Finsupp.sub_apply, hP w, w.ord_mul hf hh0]
      have := hle w
      rw [hcanω w] at this
      linarith
    · intro hmem w
      rcases hmem w with h0 | hle
      · exact absurd h0 hfh
      · have hle' : -((canonicalDivisorOf hdj - D - P) w) ≤ w.ord (f * h) := hle
        rw [Finsupp.sub_apply, Finsupp.sub_apply, hP w, w.ord_mul hf hh0] at hle'
        rw [hcanω w]
        linarith

  have step5 := ModularCurve.mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
    p hp5 N hpN K m' hm' E' hE' (f * h)
  exact step1.trans (step4.trans step5)

end S_ModularCurve_weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn
end P2MW
export P2MW.S_ModularCurve_weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn (solution)
