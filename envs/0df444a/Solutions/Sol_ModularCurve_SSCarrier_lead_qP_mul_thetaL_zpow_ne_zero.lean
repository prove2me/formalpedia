-- Prove2me | solution 1 for ModularCurve.SSCarrier.lead_qP_mul_thetaL_zpow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/68c44d1c-f3c9-5a7a-b260-c0be9c5ded38

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_SwdAlgebra
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_coe_eq_qP_mul_thetaL_jqModC_zpow_and_stackOrd_eq_zero
import Theorems.Thm_ModularCurve_evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_thetaL_jqNModC_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSCarrier_lead_qP_mul_thetaL_zpow_ne_zero
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace BMulUnit

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N]

theorem placeRamificationJ_pos {x : Place K ↥(modularFunctionFieldC K N)} (hrat : x.IsRational) (haff : IsAffineGeomPlace K N x) :
    0 < placeRamificationJ N x := by
  have h := ord_sub_evalAt_pos_of_isRational hrat haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
  unfold placeRamificationJ
  omega

theorem placeWidth_dvd (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) [CharP K p] (hpN : ¬ p ∣ N)
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K) :
    (placeWidth N x : ℤ) ∣ ((p : ℤ) + 1) / 2 := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  obtain ⟨hrat, haff, hss⟩ := hx
  set a₀ := x.evalAt (jGeomGen K N) with ha₀
  set e := placeRamificationJ N x with he
  have hepos : 0 < e := placeRamificationJ_pos hrat haff
  have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
  have hWn : placeWidth N x * e = jWidth a₀ := by
    unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
  by_cases hz : a₀ = 0
  · rw [jWidth_of_eq_zero hz] at hWn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 ⟨e, hWn.symm⟩ with hu1 | hu3
    · rw [hu1]; simp
    · have hmem : (0 : K) ∈ ssJSet p K := by rw [← hz, ha₀]; exact hss
      have hp3 := (zero_mem_ssJSet_iff p hp5 K).1 hmem
      rw [hu3]; push_cast; omega
  by_cases hs : a₀ = 1728
  · rw [jWidth_of_eq_1728 hs hz] at hWn
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).1 ⟨e, hWn.symm⟩ with hu1 | hu2
    · rw [hu1]; simp
    · have hmem : (1728 : K) ∈ ssJSet p K := by rw [← hs, ha₀]; exact hss
      have hp4 := (ofNat1728_mem_ssJSet_iff p hp5 K).1 hmem
      rw [hu2]; push_cast; omega
  · rw [jWidth_of_ne hz hs] at hWn
    rw [Nat.eq_one_of_mul_eq_one_right hWn]; simp

variable (N K) in

theorem ord_unif (x : Place K ↥(modularFunctionFieldC K N)) : x.ord (unif N K x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  exact Classical.epsilon_spec (p := fun π : ↥(modularFunctionFieldC K N) => x.ord π = 1) ⟨(π : ↥(modularFunctionFieldC K N)), x.ord_coe_irreducible hπ⟩

theorem main (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) [CharP K p] (hN : (N : K) ≠ 0)
    (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (x : ModularCurve.SSIndex p N K hp5 ((p : ℤ) + 1)) :
    ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 ((p : ℤ) + 1) x) b ≠ 0 := by
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  obtain ⟨hxss, -, -, -, -⟩ := x.2
  have hrat : x.1.IsRational := hxss.1
  have haff : IsAffineGeomPlace K N x.1 := hxss.2.1

  obtain ⟨b', hb', hss'⟩ := exists_coe_eq_qP_mul_thetaL_jqModC_zpow_and_stackOrd_eq_zero p hp5 N hpN K
  have hbb : b = b' := Subtype.ext (hb.trans hb'.symm)
  have hst : stackOrd N (((p : ℤ) + 1) / 2) b x.1 = 0 := by rw [hbb]; exact hss' x.1 haff hxss

  have hT0 : thetaL K (jqModC K) ≠ 0 := by
    have h1 := ModularCurve.thetaL_jqNModC_ne_zero K 1 (by simp)
    rwa [jqNModC_one] at h1
  have hqP0 : HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) ≠ 0 := by
    intro h0
    have h1 : SwdAlgebra.qP K = 0 := HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
    have h2 := congrArg (PowerSeries.coeff 0) h1
    simp [SwdAlgebra.qP, PowerSeries.coeff_map, PowerSeries.coeff_mk] at h2
  have hb0 : b ≠ 0 := by
    intro h0; have e := congrArg Subtype.val h0; rw [hb] at e
    exact mul_ne_zero hqP0 (zpow_ne_zero _ hT0) (by simpa using e)

  have hudvd : (placeWidth N x.1 : ℤ) ∣ ((p : ℤ) + 1) / 2 := placeWidth_dvd p hp5 hpN x.1 hxss
  have hupos : 1 ≤ placeWidth N x.1 := by
    have hepos : 0 < placeRamificationJ N x.1 := placeRamificationJ_pos hrat haff
    have hdvd := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
    have hWpos : 0 < jWidth (x.1.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> norm_num
    unfold placeWidth
    exact Nat.div_pos (Nat.le_of_dvd hWpos hdvd) hepos
  have hu0 : (placeWidth N x.1 : ℤ) ≠ 0 := by exact_mod_cast (by omega : placeWidth N x.1 ≠ 0)
  obtain ⟨c, hc⟩ := hudvd
  have ha : (placeWidth N x.1 : ℤ) * poleOrder p N K hp5 ((p : ℤ) + 1) x
      = ((p : ℤ) + 1) / 2 * ((jWidth (x.1.evalAt (jGeomGen K N)) : ℤ) - 1) := by
    have key : ∀ (u m W : ℤ), u ≠ 0 → u ∣ m → u * (m * (W - 1) / u) = m * (W - 1) := by
      intro u m W hu ⟨d, hd⟩
      rw [hd, mul_assoc, Int.mul_ediv_cancel_left _ hu]
    exact key _ _ _ hu0 ⟨c, hc⟩

  have hord : -poleOrder p N K hp5 ((p : ℤ) + 1) x ≤ x.1.ord b := by
    have e : stackOrd N (((p : ℤ) + 1) / 2) b x.1
        = (placeWidth N x.1 : ℤ) * x.1.ord b + ((p : ℤ) + 1) / 2 * ((jWidth (x.1.evalAt (jGeomGen K N)) : ℤ) - 1) := rfl
    have h2 : (placeWidth N x.1 : ℤ) * (x.1.ord b + poleOrder p N K hp5 ((p : ℤ) + 1) x) = 0 := by
      rw [mul_add, ha, ← e, hst]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hu0
    · omega

  intro hzero
  have hiff := evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd N x.1 hrat (((p : ℤ) + 1) / 2)
    (poleOrder p N K hp5 ((p : ℤ) + 1) x) hupos ha (unif N K x.1) (ord_unif K N x.1) b hb0 hord
  have h1 : 1 ≤ stackOrd N (((p : ℤ) + 1) / 2) b x.1 := hiff.1 hzero
  rw [hst] at h1
  exact absurd h1 (by norm_num)

end BMulUnit

end

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0)
    (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (x : ModularCurve.SSIndex p N K hp5 ((p : ℤ) + 1)) :
    ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 ((p : ℤ) + 1) x) b ≠ 0 :=
  BMulUnit.main p hp5 hN b hb x

end S_ModularCurve_SSCarrier_lead_qP_mul_thetaL_zpow_ne_zero
end P2MW
export P2MW.S_ModularCurve_SSCarrier_lead_qP_mul_thetaL_zpow_ne_zero (solution)
