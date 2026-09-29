-- Prove2me | solution 1 for ModularCurve.degree_eq_of_forall_eq_weightFloor_of_char_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/76ff6d38-ee57-5664-a586-6bf54ef04c3c

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_ord_jqModC_census_of_char_three
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_twelve_mul_genusFormula
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_char_three
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace Q1degChar3

theorem degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ w : Place K F, w.deg = 1) (E : Divisor K F) (U : Finset (Place K F))
    (hU : E.support ⊆ U) : E.degree = ∑ w ∈ U, E w := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset E hU]
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [hdeg w]
  · intro w _
    simp

end Q1degChar3

open Q1degChar3 in
set_option maxHeartbeats 1600000 in
theorem solution (K : Type) [Field K] [IsAlgClosed K] [CharP K 3] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (hν : nuThree N = 0) (m : ℕ)
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (7 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 6 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0)) :
    (D.degree : ℚ) = (m : ℚ) * (2 * genusFormula N - 2) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (m : ℚ) * (cuspCount N : ℚ) := by
  classical
  set j : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩ with hjdef
  have hjcoe : ((j : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) = jqModC K := rfl
  have hj0 : (j : ↥(modularFunctionFieldFullC K N)) ≠ 0 := by
    intro h
    have : jqModC K = 0 := by rw [← hjcoe, h]; rfl
    exact ModularCurve.jqModC_ne_zero_of_nontrivial K this
  haveI hcurve : IsCurveOver K ↥(modularFunctionFieldFullC K N) :=
    isCurveOver_modularFunctionFieldFullC K N
  have hdeg1 : ∀ w : Place K ↥(modularFunctionFieldFullC K N), w.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  obtain ⟨P, hP, hP0⟩ := hcurve.toHasPrincipalDivisors.exists_divisor j hj0
  set S := P.support.filter (fun w => 0 < P w) with hSdef
  set T := P.support.filter (fun w => P w < 0) with hTdef
  have hS : ∀ w, w ∈ S ↔ 0 < w.ord j := by
    intro w
    rw [hSdef, Finset.mem_filter, Finsupp.mem_support_iff, ← hP w]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.ne', h⟩
  have hT : ∀ w, w ∈ T ↔ w.ord j < 0 := by
    intro w
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, ← hP w]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.ne, h⟩
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro w hwS hwT
    have h1 := (hS w).1 hwS
    have h2 := (hT w).1 hwT
    omega
  have hPsupp : P.support ⊆ S ∪ T := by
    intro w hw
    rw [Finset.mem_union, hS, hT, ← hP w]
    rcases lt_trichotomy (P w) 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (Finsupp.mem_support_iff.mp hw)
    · exact Or.inl h

  obtain ⟨hvals, hcard13, hcard12⟩ := ord_jqModC_census_of_char_three K N hN S hS
  rw [← hjdef] at hvals hcard13 hcard12
  rw [hν] at hcard12
  have hno1 : ∀ w ∈ S, w.ord j ≠ 1 := by
    intro w hw h1
    have : w ∈ S.filter fun P => P.ord j = 1 := Finset.mem_filter.mpr ⟨hw, h1⟩
    have hc : (S.filter fun P => P.ord j = 1).card = 0 := by omega
    rw [Finset.card_eq_zero] at hc
    simp [hc] at this
  have hno2 : ∀ w ∈ S, w.ord j ≠ 2 := by
    intro w hw h2
    have : w ∈ S.filter fun P => P.ord j = 2 := Finset.mem_filter.mpr ⟨hw, h2⟩
    have hc : (S.filter fun P => P.ord j = 2).card = 0 := by omega
    rw [Finset.card_eq_zero] at hc
    simp [hc] at this
  have h36 : ∀ w ∈ S, w.ord j = 3 ∨ w.ord j = 6 := by
    intro w hw
    rcases hvals w hw with h | h | h | h
    · exact absurd h (hno1 w hw)
    · exact absurd h (hno2 w hw)
    · exact Or.inl h
    · exact Or.inr h

  have hn3 : (S.filter fun w => w.ord j = 3).card = nuTwo N := by
    rw [← hcard13]
    congr 1
    refine Finset.filter_congr fun w hw => ?_
    constructor
    · exact fun h => Or.inr h
    · rintro (h | h)
      · exact absurd h (hno1 w hw)
      · exact h

  have hdegP : P.degree = ∑ w ∈ S, P w + ∑ w ∈ T, P w := by
    rw [degree_eq_sum hdeg1 P (S ∪ T) hPsupp, Finset.sum_union hST]

  let Dp : Divisor K ↥(modularFunctionFieldFullC K N) :=
    Finsupp.onFinset P.support (fun w => max 0 (-P w)) (by
      intro w hw
      rw [Finsupp.mem_support_iff]
      intro h0
      apply hw
      simp [h0])
  have hDp : ∀ w, Dp w = max 0 (-w.ord j) := fun w => by
    simp only [Dp, Finsupp.onFinset_apply, hP w]
  have hjt : Transcendental K (j : ↥(modularFunctionFieldFullC K N)) := by
    intro halg
    apply transcendental_jqModC K
    have := halg.algHom (modularFunctionFieldFullC K N).val
    exact this
  have hfin : Module.finrank (IntermediateField.adjoin K ({j} : Set ↥(modularFunctionFieldFullC K N)))
      ↥(modularFunctionFieldFullC K N) = dedekindPsi N :=
    finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN
  haveI hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set ↥(modularFunctionFieldFullC K N)))
      ↥(modularFunctionFieldFullC K N) := by
    haveI := Module.Free.of_divisionRing
      (IntermediateField.adjoin K ({j} : Set ↥(modularFunctionFieldFullC K N))) ↥(modularFunctionFieldFullC K N)
    exact Module.finite_of_finrank_pos (by rw [hfin]; exact dedekindPsi_pos N (NeZero.ne N))
  have hpolecard := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
    (K := K) (F := ↥(modularFunctionFieldFullC K N)) j hjt Dp hDp
  have hdegDp : Dp.degree = (dedekindPsi N : ℤ) := by
    rw [hpolecard, hfin]
  have hDpsupp : Dp.support ⊆ S ∪ T := fun w hw => hPsupp (Finsupp.support_onFinset_subset hw)
  have hdegDp' : Dp.degree = ∑ w ∈ T, (-P w) := by
    rw [degree_eq_sum hdeg1 Dp (S ∪ T) hDpsupp, Finset.sum_union hST]
    have h0 : ∑ w ∈ S, Dp w = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [hDp w, ← hP w]
      have := (hS w).1 hw
      rw [← hP w] at this
      exact max_eq_left (by omega)
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hDp w, ← hP w]
    have := (hT w).1 hw
    rw [← hP w] at this
    exact max_eq_right (by omega)
  have hpole : ∑ w ∈ T, P w = -(dedekindPsi N : ℤ) := by
    have h := hdegDp.symm.trans hdegDp'
    rw [Finset.sum_neg_distrib] at h
    omega
  have hzero : ∑ w ∈ S, P w = (dedekindPsi N : ℤ) := by
    have h := hP0
    rw [hdegP, hpole] at h
    omega

  have hDsupp : D.support ⊆ S ∪ T := by
    intro w hw
    rw [Finsupp.mem_support_iff, hD w] at hw
    rw [Finset.mem_union, hS, hT]
    by_contra hcon
    push Not at hcon
    apply hw
    rw [if_neg (not_lt.mpr hcon.1), if_neg (not_lt.mpr hcon.2), add_zero]
  have hdegD : D.degree = ∑ w ∈ S, (7 * (m : ℤ) * P w) / 6 + ∑ w ∈ T, (m : ℤ) * P w := by
    rw [degree_eq_sum hdeg1 D (S ∪ T) hDsupp, Finset.sum_union hST]
    congr 1
    · refine Finset.sum_congr rfl fun w hw => ?_
      have hpos := (hS w).1 hw
      rw [hD w, if_pos hpos, if_neg (not_lt.mpr hpos.le), add_zero, hP w]
    · refine Finset.sum_congr rfl fun w hw => ?_
      have hneg := (hT w).1 hw
      rw [hD w, if_neg (not_lt.mpr hneg.le), if_pos hneg, zero_add, hP w]

  have hsumS : ∑ w ∈ S, P w
      = 3 * ((S.filter fun w => w.ord j = 3).card : ℤ)
        + 6 * ((S.filter fun w => ¬ w.ord j = 3).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun w => w.ord j = 3)]
    congr 1
    · rw [Finset.sum_congr rfl (g := fun _ => (3 : ℤ)), Finset.sum_const, nsmul_eq_mul, mul_comm]
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [hP w, hw.2]
    · rw [Finset.sum_congr rfl (g := fun _ => (6 : ℤ)), Finset.sum_const, nsmul_eq_mul, mul_comm]
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [hP w]
      exact (h36 w hw.1).resolve_left hw.2
  have hsumS' : ∑ w ∈ S, (7 * (m : ℤ) * P w) / 6
      = ((7 * (m : ℤ) * 3) / 6) * ((S.filter fun w => w.ord j = 3).card : ℤ)
        + ((7 * (m : ℤ) * 6) / 6) * ((S.filter fun w => ¬ w.ord j = 3).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun w => w.ord j = 3)]
    congr 1
    · rw [Finset.sum_congr rfl (g := fun _ => (7 * (m : ℤ) * 3) / 6), Finset.sum_const, nsmul_eq_mul,
        mul_comm]
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [hP w, hw.2]
    · rw [Finset.sum_congr rfl (g := fun _ => (7 * (m : ℤ) * 6) / 6), Finset.sum_const, nsmul_eq_mul,
        mul_comm]
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [hP w, (h36 w hw.1).resolve_left hw.2]
  have hsumT : ∑ w ∈ T, (m : ℤ) * P w = -((m : ℤ) * (dedekindPsi N : ℤ)) := by
    rw [← Finset.mul_sum, hpole, mul_neg]

  set n3 : ℕ := (S.filter fun w => w.ord j = 3).card with hn3def
  set n6 : ℕ := (S.filter fun w => ¬ w.ord j = 3).card with hn6def
  have ha3 : (7 * (m : ℤ) * 3) / 6 = 3 * (m : ℤ) + ((m / 2 : ℕ) : ℤ) := by omega
  have ha6 : (7 * (m : ℤ) * 6) / 6 = 7 * (m : ℤ) := by omega
  rw [hdegD, hsumS', hsumT, ha3, ha6]
  rw [hsumS, hn3] at hzero
  have hzQ : (3 * (nuTwo N : ℚ) + 6 * (n6 : ℚ)) = (dedekindPsi N : ℚ) := by exact_mod_cast hzero
  have h12 := twelve_mul_genusFormula N
  have hν' : (nuThree N : ℚ) = 0 := by exact_mod_cast hν
  rw [hν'] at h12 ⊢
  rw [hn3]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat]
  linear_combination (-(m : ℚ) / 6) * h12 + (7 * (m : ℚ) / 6) * hzQ

end S_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_char_three
end P2MW
export P2MW.S_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_char_three (solution)
