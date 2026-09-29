-- Prove2me | solution 1 for ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/28286694-e655-581e-a684-841256ec618c

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"

namespace ModularCurve
p2m_export "ModularCurve" "jGeomGen jGeomGen_sub_algebraMap_ne_zero ord_sub_evalAt_pos_of_isRational jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldFullC jqModC_mem_full jWidth exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC modularFunctionFieldC_eq_modularFunctionFieldFullC hasPrincipalDivisors_modularFunctionFieldC_of_perfectField ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three place_deg_eq_one_of_isAlgClosed"
namespace BridgeN
p2m_open "ModularCurve"

theorem toNat_ord_dvd_jWidth_of_eq_full
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (F : IntermediateField K (LaurentSeries K)) (hF : F = modularFunctionFieldFullC K N)
    [hPD : HasPrincipalDivisors K F] (hmem : jqModC K ∈ F) (w : Place K F) (a : K)
    (hne : (⟨jqModC K, hmem⟩ : F) - algebraMap K F a ≠ 0)
    (hpos : 0 < w.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F a)) :
    (w.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F a)).toNat ∣ jWidth a := by
  subst hF
  classical

  obtain ⟨D, hD, -⟩ := hPD.exists_divisor _ hne
  let S : Finset (Place K (modularFunctionFieldFullC K N)) := D.support.filter (fun P => 0 < D P)
  have hS : ∀ P, P ∈ S ↔ 0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)
      - algebraMap K (modularFunctionFieldFullC K N) a) := by
    intro P
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hD P]
    exact ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩

  haveI : (WeierstrassCurve.ofJ a).IsElliptic := inferInstance
  have hj : (WeierstrassCurve.ofJ a).j = a := WeierstrassCurve.ofJ_j a

  obtain ⟨f, -, hsurj, hfib, hord⟩ :=
    ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
      K N hN a (WeierstrassCurve.ofJ a) hj S hS
  obtain ⟨H, rfl⟩ := hsurj w ((hS w).mpr hpos)
  have key := WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap h2 h3
    (WeierstrassCurve.ofJ a) N f hfib H
  rw [hj] at key
  rw [hord H, Int.toNat_natCast]
  exact key

end ModularCurve.BridgeN

open ModularCurve.BridgeN in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (v : Place k ↥(modularFunctionFieldC k N))
    (a : k) (ha : v.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) = 1 := by
  classical
  by_cases hq3 : q ≤ 3
  · exact ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three q k N hqN hq3 v a ha h0 h1728
  ·
    have hjmem : jGeomGen k N ∈ v.toValuationSubring := by
      by_contra hnot
      apply h0
      rw [← ha, Place.evalAt, dif_neg hnot]
    subst ha
    have hrat : v.IsRational :=
      (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
    have hne := jGeomGen_sub_algebraMap_ne_zero k N (v.evalAt (jGeomGen k N))
    have hpos : 0 < v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (v.evalAt (jGeomGen k N))) :=
      ord_sub_evalAt_pos_of_isRational hrat hjmem hne
    have hCF : modularFunctionFieldC k N = modularFunctionFieldFullC k N :=
      ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN
    haveI : HasPrincipalDivisors k (modularFunctionFieldC k N) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
    have hNK : (N : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k q]
      exact hqN
    have hchar : ringChar k = q := ringChar.eq k q
    have h2 : ringChar k ≠ 2 := by rw [hchar]; omega
    have h3 : ringChar k ≠ 3 := by rw [hchar]; omega
    have hdvd : (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (v.evalAt (jGeomGen k N)))).toNat
        ∣ jWidth (v.evalAt (jGeomGen k N)) :=
      toNat_ord_dvd_jWidth_of_eq_full k N hNK h2 h3 (modularFunctionFieldC k N) hCF
        (jqModC_mem k N) v (v.evalAt (jGeomGen k N)) hne hpos
    have hw : jWidth (v.evalAt (jGeomGen k N)) = 1 := by
      simp [jWidth, h0, h1728]
    rw [hw, Nat.dvd_one] at hdvd
    have h := Int.toNat_of_nonneg hpos.le
    rw [hdvd] at h
    exact h.symm

#print axioms solution

end S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
end P2MW
export P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq (solution)
