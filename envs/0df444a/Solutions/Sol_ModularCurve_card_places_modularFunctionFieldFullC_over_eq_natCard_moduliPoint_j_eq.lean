-- Prove2me | solution 1 for ModularCurve.card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4e107f22-68b8-5f6a-9296-cbdc79aaa806

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve

noncomputable section

namespace P2MKcA
namespace WfromD

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := by
  intro P Q h
  rw [autPt_apply, autPt_apply] at h
  exact (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective ((castPt hγ).injective h)

section Cyclic

variable {M : Type*} [AddCommGroup M]

theorem exists_nsmul_nsmul_eq_self {N k : ℕ} (hk : k.Coprime N) {x : M} (hx : addOrderOf x = N) :
    ∃ m : ℕ, m.Coprime N ∧ m • k • x = x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hk1 : k = 1 := Nat.coprime_zero_right k |>.mp hk
    exact ⟨1, Nat.coprime_one_left 0, by rw [hk1, one_nsmul, one_nsmul]⟩
  by_cases hN1 : N = 1
  · have hx0 : x = 0 := by
      have h1 : addOrderOf x = 1 := by rw [hx, hN1]
      exact AddMonoid.addOrderOf_eq_one_iff.mp h1
    exact ⟨1, Nat.coprime_one_left N, by rw [hx0, smul_zero, smul_zero]⟩
  · have h1N : 1 < N := by omega
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1N
    have hNx : N • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
    have hdiv : N * (k * m / N) + 1 = k * m := by
      have h := Nat.div_add_mod (k * m) N
      rw [hm] at h
      exact h
    refine ⟨m, ?_, ?_⟩
    · have hdm : Nat.gcd m N ∣ N * (k * m / N) + 1 := by
        rw [hdiv]; exact Dvd.dvd.mul_left (Nat.gcd_dvd_left m N) k
      have hdN : Nat.gcd m N ∣ N * (k * m / N) := Dvd.dvd.mul_right (Nat.gcd_dvd_right m N) _
      exact Nat.dvd_one.mp ((Nat.dvd_add_right hdN).mp hdm)
    · rw [← mul_nsmul x k m, ← hdiv, add_nsmul, mul_nsmul x N (k * m / N), hNx, smul_zero, zero_add,
        one_nsmul]

theorem zmultiples_nsmul_eq_of_coprime {N k : ℕ} (hk : k.Coprime N) {x : M} (hx : addOrderOf x = N) :
    AddSubgroup.zmultiples (k • x) = AddSubgroup.zmultiples x := by
  obtain ⟨m, -, hm⟩ := exists_nsmul_nsmul_eq_self hk hx
  refine le_antisymm ?_ ?_
  · rintro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n * (k : ℤ), by rw [mul_zsmul, natCast_zsmul]⟩
  · rintro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n * (m : ℤ), by rw [mul_zsmul, natCast_zsmul, hm]⟩

theorem exists_coprime_nsmul_of_zmultiples_eq {N : ℕ} (hN : N ≠ 0) {x y : M} (hx : addOrderOf x = N)
    (hy : addOrderOf y = N) (h : AddSubgroup.zmultiples y = AddSubgroup.zmultiples x) :
    ∃ k : ℕ, k.Coprime N ∧ y = k • x := by
  have hy' : y ∈ AddSubgroup.zmultiples x := by rw [← h]; exact AddSubgroup.mem_zmultiples y
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy'
  have hNx : (N : ℤ) • x = 0 := by rw [natCast_zsmul, ← hx]; exact addOrderOf_nsmul_eq_zero x
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m % N :=
    ⟨(m % N).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN))⟩
  have hmk : m • x = k • x := by
    have : m = m % N + N * (m / N) := (Int.emod_add_mul_ediv m N).symm
    rw [← natCast_zsmul, hk]
    conv_lhs => rw [this]
    rw [add_zsmul, mul_zsmul', hNx, zsmul_zero, add_zero]
  refine ⟨k, ?_, hmk⟩
  have hzk : AddSubgroup.zmultiples (k • x) = AddSubgroup.zmultiples x := by rw [← hmk]; exact h
  have hxmem : x ∈ AddSubgroup.zmultiples (k • x) := by rw [hzk]; exact AddSubgroup.mem_zmultiples x
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hxmem
  have hz : (j * k - 1 : ℤ) • x = 0 := by
    rw [sub_zsmul, one_zsmul, mul_zsmul, natCast_zsmul, hj]; simp
  have hdvd : (N : ℤ) ∣ j * k - 1 := by
    rw [← hx]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  obtain ⟨t, ht⟩ := hdvd
  have hcop : IsCoprime (k : ℤ) (N : ℤ) := ⟨j, -t, by linear_combination ht⟩
  have hg : Int.gcd (k : ℤ) (N : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  simpa [Int.gcd_natCast_natCast] using hg

theorem zmultiples_eq_of_mem_of_addOrderOf_eq {N : ℕ} (hN : N ≠ 0) {x y : M} (hx : addOrderOf x = N)
    (hy : addOrderOf y = N) (h : y ∈ AddSubgroup.zmultiples x) :
    AddSubgroup.zmultiples y = AddSubgroup.zmultiples x := by
  have hle : AddSubgroup.zmultiples y ≤ AddSubgroup.zmultiples x := by
    rw [AddSubgroup.zmultiples_le]; exact h
  haveI : Finite (AddSubgroup.zmultiples x) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hx]; exact hN
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zmultiples, Nat.card_zmultiples, hx, hy]

end Cyclic

section Count

variable (W : WeierstrassCurve L) (N : ℕ)

abbrev CycSub : Type _ := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

abbrev OrdPt : Type _ := {T : W.toAffine.Point // addOrderOf T = N}

def R (T T' : OrdPt W N) : Prop :=
  ∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
    HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1)

def Rel (H H' : CycSub W N) : Prop :=
  ∃ γ : VariableChange L, γ • W = W ∧
    ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T'

def cyc (T : OrdPt W N) : CycSub W N :=
  ⟨AddSubgroup.zmultiples T.1, ⟨⟨T.1, AddSubgroup.mem_zmultiples T.1⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, T.2]⟩

variable {W N}

theorem R_iff (T T' : OrdPt W N) :
    R W N T T' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
      T'.1 = k • autPt γ hγ T.1 := by
  unfold R
  refine exists_congr (fun γ => exists_congr (fun hγ => exists_congr (fun k => and_congr_right (fun _ => ?_))))
  rw [autPt_apply, ← map_nsmul (castPt hγ), eq_comm, castPt_eq_iff_heq]
  exact heq_comm

theorem Rel_iff (H H' : CycSub W N) :
    Rel W N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • W = W, ∀ T ∈ H.1, autPt γ hγ T ∈ H'.1 := by
  unfold Rel
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun T hT => ?_⟩
    obtain ⟨T', hT', hh⟩ := h T hT
    rwa [(autPt_eq_iff_heq γ hγ T T').mpr hh]
  · rintro ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, fun T hT => ⟨autPt γ hγ T, h T hT, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩

private theorem _root_.P2MKcA.WfromD.exists_generator (hN : N ≠ 0) (H : CycSub W N) :
    ∃ T : W.toAffine.Point, addOrderOf T = N ∧ AddSubgroup.zmultiples T = H.1 := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
  have hfin : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hog : addOrderOf g = N := (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcard
  refine ⟨g.1, by rw [AddSubgroup.addOrderOf_coe, hog], ?_⟩
  have hle : AddSubgroup.zmultiples (g.1) ≤ H.1 := by
    rw [AddSubgroup.zmultiples_le]; exact g.2
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hog]

p2m_export "P2MKcA.WfromD" "exists_generator"
theorem addOrderOf_autPt (γ : VariableChange L) (hγ : γ • W = W) (T : W.toAffine.Point) :
    addOrderOf (autPt γ hγ T) = addOrderOf T :=
  addOrderOf_injective (autPt γ hγ) (autPt_injective γ hγ) T

theorem rel_cyc_of_R {T T' : OrdPt W N} (h : R W N T T') : Rel W N (cyc W N T) (cyc W N T') := by
  rw [R_iff] at h
  obtain ⟨γ, hγ, k, hk, hkT⟩ := h
  rw [Rel_iff]
  refine ⟨γ, hγ, fun P hP => ?_⟩
  change P ∈ AddSubgroup.zmultiples T.1 at hP
  change autPt γ hγ P ∈ AddSubgroup.zmultiples T'.1
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
  have hord : addOrderOf (autPt γ hγ T.1) = N := by rw [addOrderOf_autPt, T.2]
  rw [hkT, zmultiples_nsmul_eq_of_coprime hk hord, map_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) n

theorem R_of_rel_cyc (hN : N ≠ 0) {T T' : OrdPt W N} (h : Rel W N (cyc W N T) (cyc W N T')) :
    R W N T T' := by
  rw [Rel_iff] at h
  obtain ⟨γ, hγ, hmem⟩ := h
  have hP : autPt γ hγ T.1 ∈ AddSubgroup.zmultiples T'.1 := hmem T.1 (AddSubgroup.mem_zmultiples T.1)
  have hord : addOrderOf (autPt γ hγ T.1) = N := by rw [addOrderOf_autPt, T.2]
  have hgen : AddSubgroup.zmultiples (autPt γ hγ T.1) = AddSubgroup.zmultiples T'.1 :=
    zmultiples_eq_of_mem_of_addOrderOf_eq hN T'.2 hord hP
  obtain ⟨k, hk, hkT⟩ := exists_coprime_nsmul_of_zmultiples_eq hN hord T'.2 hgen.symm
  rw [R_iff]
  exact ⟨γ, hγ, k, hk, hkT⟩

theorem natCard_quot_R_eq_card_of_orbitMap (hN : N ≠ 0) {P : Type*} (S : Finset P)
    (f : CycSub W N → P) (hfS : ∀ H, f H ∈ S) (hsurj : ∀ p ∈ S, ∃ H, f H = p)
    (hfib : ∀ H H', f H = f H' ↔ Rel W N H H') :
    Nat.card (Quot (R W N)) = S.card := by
  classical
  let F : Quot (R W N) → {p // p ∈ S} :=
    Quot.lift (fun T => ⟨f (cyc W N T), hfS _⟩)
      (fun T T' h => Subtype.ext ((hfib _ _).mpr (rel_cyc_of_R h)))
  have hF : Function.Bijective F := by
    constructor
    · intro a b
      induction a using Quot.ind with | _ T => ?_
      induction b using Quot.ind with | _ T' => ?_
      intro hab
      have hab' : f (cyc W N T) = f (cyc W N T') := congrArg Subtype.val hab
      exact Quot.sound (R_of_rel_cyc hN ((hfib _ _).mp hab'))
    · rintro ⟨p, hp⟩
      obtain ⟨H, hH⟩ := hsurj p hp
      obtain ⟨T, hT, hTH⟩ := exists_generator hN H
      refine ⟨Quot.mk _ ⟨T, hT⟩, Subtype.ext ?_⟩
      show f (cyc W N ⟨T, hT⟩) = p
      rw [← hH]
      congr 1
      exact Subtype.ext hTH
  rw [Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_coe]

end Count

end P2MKcA.WfromD

end

open P2MKcA.WfromD in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (j₀ : K) (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔
      0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
        algebraMap K (modularFunctionFieldFullC K N) j₀)) :
    S.card = Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀} := by
  have hN0 : N ≠ 0 := NeZero.ne N

  set E₀ : WeierstrassCurve K := WeierstrassCurve.ofJ j₀ with hE₀
  haveI : E₀.IsElliptic := by rw [hE₀]; infer_instance
  have hj : E₀.j = j₀ := WeierstrassCurve.ofJ_j j₀

  obtain ⟨f, hfS, hsurj, hfib, -⟩ :=
    ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
      K N hN j₀ E₀ hj S hS

  have h1 : Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀} = Nat.card (Quot (R E₀ N)) := by
    have e : Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀}
        = Nat.card {x : ModuliPoint N K // ModuliPoint.j x = E₀.j} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hj]))
    rw [e]
    exact ModularCurve.natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq N K E₀

  have h2 : Nat.card (Quot (R E₀ N)) = S.card :=
    natCard_quot_R_eq_card_of_orbitMap (W := E₀) (N := N) hN0 S f hfS hsurj
      (fun H H' => (hfib H H').trans Iff.rfl)
  rw [h1, h2]

end S_ModularCurve_card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq
end P2MW
export P2MW.S_ModularCurve_card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq (solution)
