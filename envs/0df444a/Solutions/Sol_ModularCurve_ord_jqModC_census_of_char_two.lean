-- Prove2me | solution 1 for ModularCurve.ord_jqModC_census_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/987ba7b3-2841-52c9-890a-f8ffdc655f27

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve
import Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
import Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_char_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jqModC_census_of_char_two
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
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcCEN2

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem two_eq_zero : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

theorem three_eq_one : (3 : K) = 1 := by
  have : (3 : K) = 2 + 1 := by norm_num
  rw [this, two_eq_zero, zero_add]

theorem neg_eq (a : K) : -a = a := by
  have h : a + a = 0 := by rw [← two_mul, two_eq_zero, zero_mul]
  exact (neg_eq_of_add_eq_zero_left h)

theorem sub_eq_add' (a b : K) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq]

theorem add_self (a : K) : a + a = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem sq_add (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  rw [this, two_eq_zero, zero_mul, add_zero]

theorem sq_add_self_eq_zero_iff (x : K) : x ^ 2 + x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have : x * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · right
      have := neg_eq (1 : K)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · ring
    · have := add_self (1 : K); simpa [sq] using this

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem omega_pow_three : ω ^ 3 = 1 := by
  have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h1
  linear_combination -h1

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have : (3 : K) = 0 := by linear_combination hω
  rw [three_eq_one] at this
  exact one_ne_zero this

theorem omega_ne_zero : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

theorem omega_sq : ω ^ 2 = ω + 1 := by
  have h1 := neg_eq ω
  have h2 := neg_eq (1 : K)
  linear_combination hω + h1 + h2

theorem sq_add_self_add_one_eq_zero_iff (x : K) : x ^ 2 + x + 1 = 0 ↔ x = ω ∨ x = ω + 1 := by
  constructor
  · intro h
    have : (x + ω) * (x + ω + 1) = 0 := by
      have h2 := two_eq_zero (K := K)
      linear_combination h + hω + (x * ω - 1) * h2
    rcases mul_eq_zero.mp this with h0 | h1
    · left
      have := neg_eq ω
      linear_combination h0 + this
    · right
      have := neg_eq (ω + 1)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · exact hω
    · have h2 := two_eq_zero (K := K)
      linear_combination hω + (ω + 1) * h2

end CharTwo

section Curve

variable (K : Type*) [Field K] [CharP K 2]

def E₀ : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

@[scoped simp] theorem E₀_a₁ : (E₀ K).a₁ = 0 := rfl
@[scoped simp] theorem E₀_a₂ : (E₀ K).a₂ = 0 := rfl
@[scoped simp] theorem E₀_a₃ : (E₀ K).a₃ = 1 := rfl
@[scoped simp] theorem E₀_a₄ : (E₀ K).a₄ = 0 := rfl
@[scoped simp] theorem E₀_a₆ : (E₀ K).a₆ = 0 := rfl

theorem E₀_Δ : (E₀ K).Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, E₀_a₁, E₀_a₂, E₀_a₃, E₀_a₄, E₀_a₆]
  have h2 := two_eq_zero (K := K)
  linear_combination (-14 : K) * h2

scoped instance E₀_isElliptic : (E₀ K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, E₀_Δ]; exact isUnit_one

theorem E₀_c₄ : (E₀ K).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, E₀_a₁, E₀_a₂, E₀_a₃,
    E₀_a₄]
  ring

theorem E₀_j : (E₀ K).j = 0 := by
  rw [WeierstrassCurve.j, E₀_c₄]; ring

variable {K}

theorem smul_E₀_eq_iff (γ : VariableChange K) :
    γ • E₀ K = E₀ K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 3 := by
  have h2 := two_eq_zero (K := K)
  have h3 := three_eq_one (K := K)
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have hui : ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) = 1 := by simp
  have hv : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.u⁻¹).ne_zero
  constructor
  · intro h
    have e₂ := congrArg WeierstrassCurve.a₂ h
    have e₃ := congrArg WeierstrassCurve.a₃ h
    have e₄ := congrArg WeierstrassCurve.a₄ h
    have e₆ := congrArg WeierstrassCurve.a₆ h
    simp only [E₀, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆] at e₂ e₃ e₄ e₆

    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      linear_combination e₃ - ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    have hu3 : (γ.u : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hv3, one_mul] at this

    have hr : γ.r = γ.s ^ 2 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((3 : K) * γ.r - γ.s ^ 2) = 0 := by linear_combination e₂
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) hv
      · rw [h3, one_mul, sub_eq_zero] at h0
        exact h0

    have hs : γ.s ^ 4 = γ.s := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-γ.s + (3 : K) * γ.r ^ 2 - 2 * γ.s * γ.t) = 0 := by
        linear_combination e₄
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h0) hv
      · rw [h3, h2, hr] at h0
        linear_combination h0

    have ht : γ.t ^ 2 + γ.t = γ.s ^ 3 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (γ.r ^ 3 - γ.t - γ.t ^ 2) = 0 := by linear_combination e₆
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 6) (by norm_num) |>.mp h0) hv
      · rw [hr] at h0
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 4 * γ.s ^ 2 := by ring
        rw [e, hs] at h0
        linear_combination -h0
    exact ⟨hu3, hr, hs, ht⟩
  · rintro ⟨hu3, hr, hs, ht⟩
    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hu3, mul_one] at this
    have hs3 : γ.s ^ 6 = γ.s ^ 3 := by
      calc γ.s ^ 6 = γ.s ^ 4 * γ.s ^ 2 := by ring
        _ = γ.s ^ 3 := by rw [hs]; ring
    have hns := neg_eq γ.s
    have hn1 := neg_eq γ.t
    have hn2 := neg_eq (γ.t ^ 2)
    have hss : γ.s + γ.s ^ 4 = 0 := by rw [hs, add_self]
    ext
    · simp only [variableChange_a₁, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · simp only [variableChange_a₂, E₀]
      rw [h3, hr]; ring
    · simp only [variableChange_a₃, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2 + hv3
    · simp only [variableChange_a₄, E₀]
      rw [h2, h3, hr]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 4 * hss - ((γ.u⁻¹ : Kˣ) : K) ^ 4 * γ.s * h2
    · simp only [variableChange_a₆, E₀]
      rw [hr]
      have : (γ.s ^ 2) ^ 3 - γ.t * 1 - γ.t ^ 2 = 0 := by
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 6 := by ring
        rw [e, hs3, ← ht]
        ring
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * this

end Curve

section Explicit

variable {K : Type*} [Field K] [CharP K 2]

def ε : VariableChange K := ⟨1, 0, 0, 1⟩

def αv (ω : K) : VariableChange K := ⟨1, 1, 1, ω⟩

def βv (u : Kˣ) : VariableChange K := ⟨u, 0, 0, 0⟩

@[scoped simp] theorem ε_u : (ε : VariableChange K).u = 1 := rfl
@[scoped simp] theorem ε_r : (ε : VariableChange K).r = 0 := rfl
@[scoped simp] theorem ε_s : (ε : VariableChange K).s = 0 := rfl
@[scoped simp] theorem ε_t : (ε : VariableChange K).t = 1 := rfl
@[scoped simp] theorem αv_u (ω : K) : (αv ω).u = 1 := rfl
@[scoped simp] theorem αv_r (ω : K) : (αv ω).r = 1 := rfl
@[scoped simp] theorem αv_s (ω : K) : (αv ω).s = 1 := rfl
@[scoped simp] theorem αv_t (ω : K) : (αv ω).t = ω := rfl
@[scoped simp] theorem βv_u (u : Kˣ) : (βv u).u = u := rfl
@[scoped simp] theorem βv_r (u : Kˣ) : (βv u).r = 0 := rfl
@[scoped simp] theorem βv_s (u : Kˣ) : (βv u).s = 0 := rfl
@[scoped simp] theorem βv_t (u : Kˣ) : (βv u).t = 0 := rfl

section MulComponents
variable {R : Type*} [CommRing R] (C C' : VariableChange R)
theorem mul_u : (C * C').u = C.u * C'.u := rfl
theorem mul_r : (C * C').r = C.r * (C'.u : R) ^ 2 + C'.r := rfl
theorem mul_s : (C * C').s = (C'.u : R) * C.s + C'.s := rfl
theorem mul_t : (C * C').t = C.t * (C'.u : R) ^ 3 + C.r * C'.s * (C'.u : R) ^ 2 + C'.t := rfl
@[scoped simp] theorem one_u : (1 : VariableChange R).u = 1 := rfl
@[scoped simp] theorem one_r : (1 : VariableChange R).r = 0 := rfl
@[scoped simp] theorem one_s : (1 : VariableChange R).s = 0 := rfl
@[scoped simp] theorem one_t : (1 : VariableChange R).t = 0 := rfl
end MulComponents

theorem ε_smul : (ε : VariableChange K) • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp, by simp, by simp, by simpa using add_self (1 : K)⟩

theorem ε_mul_ε : (ε : VariableChange K) * ε = 1 := by
  ext
  · simp [mul_u]
  · simp [mul_r]
  · simp [mul_s]
  · simp only [mul_t, ε_t, ε_u, ε_r, one_t, Units.val_one]; simpa using add_self (1 : K)

theorem ε_sq : (ε : VariableChange K) ^ 2 = 1 := by rw [sq, ε_mul_ε]

theorem ε_ne_one : (ε : VariableChange K) ≠ 1 := by
  intro h; have := congrArg VariableChange.t h; simp at this

theorem orderOf_ε : orderOf (ε : VariableChange K) = 2 :=
  orderOf_eq_prime ε_sq ε_ne_one

theorem mul_ε_comm {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) : γ * ε = ε * γ := by
  obtain ⟨hu3, -, -, -⟩ := (smul_E₀_eq_iff γ).1 hγ
  ext
  · simp [mul_u]
  · simp [mul_r]
  · simp [mul_s]
  · simp only [mul_t, ε_t, ε_u, ε_r, ε_s, Units.val_one, hu3]; ring

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem αv_smul : αv ω • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp, by simp, by simp, by
    simp only [αv_t, αv_s, one_pow]
    have := neg_eq (1 : K)
    linear_combination hω + this⟩

theorem αv_sq : αv ω ^ 2 = ε := by
  rw [sq]
  ext
  · simp [mul_u]
  · simp only [mul_r, αv_r, αv_u, Units.val_one, ε_r]; simpa using add_self (1 : K)
  · simp only [mul_s, αv_s, αv_u, Units.val_one, ε_s]; simpa using add_self (1 : K)
  · simp only [mul_t, αv_t, αv_u, αv_r, αv_s, Units.val_one, ε_t]
    have := add_self ω
    linear_combination this

theorem αv_ne_one : αv ω ≠ 1 := by
  intro h; have := congrArg VariableChange.r h; simp at this

theorem αv_ne_ε : αv ω ≠ ε := by
  intro h; have := congrArg VariableChange.r h; simp at this

omit hω in
theorem βv_smul (u : Kˣ) (hu : (u : K) ^ 3 = 1) : βv u • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simpa using hu, by simp, by simp, by simp⟩

omit hω in
theorem βv_pow_three (u : Kˣ) (hu : (u : K) ^ 3 = 1) : βv u ^ 3 = 1 := by
  have hu' : u ^ 3 = 1 := Units.ext (by simpa using hu)
  rw [pow_succ, sq]
  ext
  · simp only [mul_u, βv_u, one_u]; rw [← hu']; simp [pow_succ]
  · simp [mul_r]
  · simp [mul_s]
  · simp [mul_t]

omit hω in
theorem βv_ne_one (u : Kˣ) (hu1 : (u : K) ≠ 1) : βv u ≠ 1 := by
  intro h; have := congrArg VariableChange.u h
  simp only [βv_u, one_u] at this
  exact hu1 (by simp [this])

omit hω in
theorem βv_ne_ε (u : Kˣ) (hu1 : (u : K) ≠ 1) : βv u ≠ ε := by
  intro h; have := congrArg VariableChange.u h
  simp only [βv_u, ε_u] at this
  exact hu1 (by simp [this])

omit hω in

theorem sq_or_cube_mem {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) :
    γ ^ 2 = 1 ∨ γ ^ 2 = ε ∨ γ ^ 3 = 1 ∨ γ ^ 3 = ε := by
  obtain ⟨hu3, hr, hs, ht⟩ := (smul_E₀_eq_iff γ).1 hγ
  have h2 := two_eq_zero (K := K)

  have hs3 : γ.s ^ 3 = 0 ∨ γ.s ^ 3 = 1 := by
    have : γ.s * (γ.s ^ 3 - 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp this with h0 | h0
    · left; rw [h0]; ring
    · right; exact sub_eq_zero.mp h0
  by_cases hu1 : (γ.u : K) = 1
  ·
    have hU : γ.u = 1 := Units.ext (by simpa using hu1)
    have key : ∀ c : K, γ.s ^ 3 = c → γ ^ 2 = (⟨1, 0, 0, c⟩ : VariableChange K) := by
      intro c hc
      rw [sq]
      ext
      · simp [mul_u, hU]
      · simp only [mul_r, hU, Units.val_one]; linear_combination γ.r * h2
      · simp only [mul_s, hU, Units.val_one]; linear_combination γ.s * h2
      · simp only [mul_t, hU, Units.val_one, hr]; rw [← hc]; linear_combination γ.t * h2
    rcases hs3 with h0 | h1
    · exact Or.inl (by rw [key 0 h0]; rfl)
    · exact Or.inr (Or.inl (by rw [key 1 h1]; rfl))
  ·
    have hq : (γ.u : K) ^ 2 + (γ.u : K) + 1 = 0 := by
      have : ((γ.u : K) - 1) * ((γ.u : K) ^ 2 + (γ.u : K) + 1) = 0 := by
        linear_combination hu3
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hu1
      · exact h0
    have hU3 : γ.u ^ 3 = 1 := Units.ext (by simpa using hu3)

    set c : K := γ.s ^ 3 * (γ.u : K) + γ.t with hc
    have hcc : c ^ 2 + c = 0 := by
      rcases hs3 with h0 | h1
      ·
        have hs0 : γ.s = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h0
        have : c = γ.t := by rw [hc, hs0]; ring
        rw [this, ht, hs0]; ring
      · have ht1 : γ.t ^ 2 + γ.t = 1 := by rw [ht, h1]
        rw [hc, h1, one_mul]
        linear_combination hq + ht1 + ((γ.u : K) * γ.t) * h2
    have key : γ ^ 3 = (⟨1, 0, 0, c⟩ : VariableChange K) := by
      have hu4 : (γ.u : K) ^ 4 = (γ.u : K) := by
        calc (γ.u : K) ^ 4 = (γ.u : K) ^ 3 * (γ.u : K) := by ring
          _ = (γ.u : K) := by rw [hu3, one_mul]
      rw [pow_succ, sq]
      ext
      · simp only [mul_u]; rw [← hU3]; push_cast; ring
      · simp only [mul_r, mul_u, Units.val_mul]
        have : γ.r * ((γ.u : K) ^ 4 + (γ.u : K) ^ 2 + 1) = 0 := by
          rw [hu4]; linear_combination γ.r * hq
        linear_combination this
      · simp only [mul_s, mul_u, Units.val_mul]
        linear_combination γ.s * hq
      · simp only [mul_t, mul_r, mul_s, mul_u, Units.val_mul]
        rw [hc, hr]
        linear_combination (γ.t * ((γ.u : K) ^ 3 + 1) + γ.t + γ.s ^ 3 * (γ.u : K) ^ 2 +
          γ.s ^ 3 * (γ.u : K)) * hu3 + (γ.t + γ.s ^ 3 * (γ.u : K) ^ 2) * h2
    rcases (sq_add_self_eq_zero_iff c).1 hcc with h0 | h1
    · exact Or.inr (Or.inr (Or.inl (by rw [key, h0]; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [key, h1]; rfl)))

end Explicit

section Count

variable {K : Type*} [Field K] [CharP K 2]

abbrev Γ (K : Type*) [Field K] [CharP K 2] : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) (E₀ K)

theorem mem_Γ_iff (γ : VariableChange K) : γ ∈ Γ K ↔ γ • E₀ K = E₀ K := MulAction.mem_stabilizer_iff

abbrev Param (K : Type*) [Field K] : Type _ :=
  {p : Kˣ × (K × K) // (p.1 : K) ^ 3 = 1 ∧ (p.2.1 ^ 4 = p.2.1 ∧ p.2.2 ^ 2 + p.2.2 = p.2.1 ^ 3)}

def ΓEquivParam : Γ K ≃ Param K where
  toFun γ := ⟨(γ.1.u, (γ.1.s, γ.1.t)),
    ⟨((smul_E₀_eq_iff γ.1).1 γ.2).1, ((smul_E₀_eq_iff γ.1).1 γ.2).2.2⟩⟩
  invFun p := ⟨⟨p.1.1, p.1.2.1 ^ 2, p.1.2.1, p.1.2.2⟩,
    (mem_Γ_iff _).2 ((smul_E₀_eq_iff _).2 ⟨p.2.1, rfl, p.2.2.1, p.2.2.2⟩)⟩
  left_inv γ := by
    obtain ⟨γ, hγ⟩ := γ
    obtain ⟨-, hr, -, -⟩ := (smul_E₀_eq_iff γ).1 hγ
    apply Subtype.ext
    ext <;> simp [hr]
  right_inv p := by
    obtain ⟨⟨u, s, t⟩, hp⟩ := p
    rfl

theorem pow_four_eq_self_iff (s : K) : s ^ 4 = s ↔ s = 0 ∨ s ^ 3 = 1 := by
  constructor
  · intro h
    have : s * (s ^ 3 - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  · rintro (rfl | h)
    · ring
    · linear_combination s * h

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := orderOf_eq_prime (omega_pow_three ω hω) (omega_ne_one ω hω)
  rw [← h]; exact IsPrimitiveRoot.orderOf ω

theorem natCard_units_cube : Nat.card {u : Kˣ // (u : K) ^ 3 = 1} = 3 := by
  have e : {u : Kˣ // (u : K) ^ 3 = 1} ≃ rootsOfUnity 3 K :=
    Equiv.subtypeEquivRight (fun u => by
      rw [mem_rootsOfUnity]
      constructor
      · intro h; exact Units.ext (by simpa using h)
      · intro h; have := congrArg Units.val h; simpa using this)
  rw [Nat.card_congr e]
  exact (isPrimitiveRoot_omega ω hω).card_rootsOfUnity

theorem natCard_pow_four_eq_self [DecidableEq K] : Nat.card {s : K // s ^ 4 = s} = 4 := by
  have h3 := (isPrimitiveRoot_omega ω hω).card_nthRootsFinset
  set F : Finset K := Polynomial.nthRootsFinset 3 (1 : K) with hF
  have hmem : ∀ s : K, s ^ 4 = s ↔ s ∈ insert (0 : K) F := by
    intro s
    rw [pow_four_eq_self_iff, Finset.mem_insert, hF, Polynomial.mem_nthRootsFinset (by norm_num)]
  have e : {s : K // s ^ 4 = s} ≃ (insert (0 : K) F : Finset K) := Equiv.subtypeEquivRight hmem
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, Finset.card_insert_of_notMem, h3]
  rw [hF, Polynomial.mem_nthRootsFinset (by norm_num)]
  norm_num

theorem t_values [DecidableEq K] {s t : K} (hs : s ^ 4 = s) :
    t ^ 2 + t = s ^ 3 ↔ t = (if s = 0 then 0 else ω) ∨ t = (if s = 0 then 0 else ω) + 1 := by
  by_cases h0 : s = 0
  · simp only [h0, if_true, zero_add]
    have : (0 : K) ^ 3 = 0 := by ring
    rw [this]
    exact sq_add_self_eq_zero_iff t
  · simp only [h0, if_false]
    have hs3 : s ^ 3 = 1 := ((pow_four_eq_self_iff s).1 hs).resolve_left h0
    rw [hs3, ← sq_add_self_add_one_eq_zero_iff ω hω t]
    have h2 := two_eq_zero (K := K)
    constructor
    · intro h; linear_combination h + h2
    · intro h; linear_combination h - h2

theorem natCard_st [DecidableEq K] :
    Nat.card {q : K × K // q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3} = 8 := by
  set base : K → K := fun s => if s = 0 then 0 else ω with hbase
  have e : {q : K × K // q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3} ≃ {s : K // s ^ 4 = s} × Bool :=
    { toFun := fun q => (⟨q.1.1, q.2.1⟩, decide (q.1.2 = base q.1.1 + 1))
      invFun := fun p => ⟨(p.1.1, base p.1.1 + if p.2 then 1 else 0),
        ⟨p.1.2, (t_values ω hω p.1.2).2 (by cases p.2 <;> simp [hbase])⟩⟩
      left_inv := by
        rintro ⟨⟨s, t⟩, hs, ht⟩
        dsimp only at hs ht
        apply Subtype.ext
        simp only [Prod.mk.injEq, true_and]
        rcases (t_values ω hω hs).1 ht with h | h
        · have hne : ¬ (t = base s + 1) := by
            rw [h]; intro h'
            have : (1 : K) = 0 := by linear_combination -h'
            exact one_ne_zero this
          simp only [hne, decide_false]
          rw [h]; simp [hbase]
        · simp only [h, decide_true]
          simp [hbase]
      right_inv := by
        rintro ⟨⟨s, hs⟩, b⟩
        apply Prod.ext
        · exact Subtype.ext rfl
        · cases b
          · show decide (base s + (if false = true then (1 : K) else 0) = base s + 1) = false
            simp
          · show decide (base s + (if true = true then (1 : K) else 0) = base s + 1) = true
            simp }
  rw [Nat.card_congr e, Nat.card_prod, natCard_pow_four_eq_self ω hω]
  simp

theorem natCard_Γ : Nat.card (Γ K) = 24 := by
  classical
  have e : Param K ≃ {u : Kˣ // (u : K) ^ 3 = 1} × {q : K × K // q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3} :=
    Equiv.subtypeProdEquivProd (p := fun u : Kˣ => (u : K) ^ 3 = 1)
      (q := fun q : K × K => q.1 ^ 4 = q.1 ∧ q.2 ^ 2 + q.2 = q.1 ^ 3)
  rw [Nat.card_congr ΓEquivParam, Nat.card_congr e, Nat.card_prod, natCard_units_cube ω hω,
    natCard_st ω hω]

include hω in
theorem finite_Γ' : Finite (Γ K) := by
  classical
  exact Nat.finite_of_card_ne_zero (by rw [natCard_Γ ω hω]; norm_num)

end Count

section GroupG

variable {K : Type*} [Field K] [CharP K 2]

def εΓ : Γ K := ⟨ε, (mem_Γ_iff _).2 ε_smul⟩

@[scoped simp] theorem coe_εΓ : ((εΓ : Γ K) : VariableChange K) = ε := rfl

theorem orderOf_εΓ : orderOf (εΓ : Γ K) = 2 := by
  rw [← Subgroup.orderOf_coe, coe_εΓ, orderOf_ε]

theorem εΓ_mem_center : (εΓ : Γ K) ∈ Subgroup.center (Γ K) := by
  rw [Subgroup.mem_center_iff]
  intro γ
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_εΓ]
  exact mul_ε_comm ((mem_Γ_iff _).1 γ.2)

abbrev Zε (K : Type*) [Field K] [CharP K 2] : Subgroup (Γ K) := Subgroup.zpowers (εΓ : Γ K)

scoped instance Zε_normal : (Zε K).Normal :=
  ⟨fun n hn g => by
    have hc : n ∈ Subgroup.center (Γ K) := (Subgroup.zpowers_le.mpr εΓ_mem_center) hn
    rw [Subgroup.mem_center_iff] at hc
    rw [hc g, mul_inv_cancel_right]; exact hn⟩

theorem natCard_Zε : Nat.card (Zε K) = 2 := by
  rw [Nat.card_zpowers, orderOf_εΓ]

theorem mem_Zε_iff (γ : Γ K) : γ ∈ Zε K ↔ (γ : VariableChange K) = 1 ∨ (γ : VariableChange K) = ε := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : (εΓ : Γ K) ^ (2 : ℤ) = 1 := by
      have := pow_orderOf_eq_one (εΓ : Γ K)
      rw [orderOf_εΓ] at this
      exact_mod_cast this
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      have : (εΓ : Γ K) ^ (m + m) = 1 := by
        rw [← two_mul, zpow_mul, h2, one_zpow]
      rw [this]; rfl
    · right
      have : (εΓ : Γ K) ^ (2 * m + 1) = εΓ := by
        rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
      rw [this]; rfl
  · rintro (h | h)
    · exact ⟨0, by rw [zpow_zero]; exact Subtype.ext h.symm⟩
    · exact ⟨1, by rw [zpow_one]; exact Subtype.ext h.symm⟩

abbrev G (K : Type*) [Field K] [CharP K 2] : Type _ := Γ K ⧸ Zε K

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem natCard_G : Nat.card (G K) = 12 := by
  have h : Nat.card (Γ K) = Nat.card (G K) * Nat.card (Zε K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Zε K)
  rw [natCard_Γ ω hω, natCard_Zε] at h
  omega

include hω in
theorem finite_G : Finite (G K) := by
  haveI := finite_Γ' ω hω (K := K)
  infer_instance

omit hω in

theorem G_sq_or_cube (g : G K) : g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    have hγ := (mem_Γ_iff _).1 γ.2
    have key : ∀ n : ℕ, ((γ : VariableChange K) ^ n = 1 ∨ (γ : VariableChange K) ^ n = ε) →
        ((γ : G K)) ^ n = 1 := by
      intro n hn
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_Zε_iff]
      simpa using hn
    rcases sq_or_cube_mem hγ with h | h | h | h
    · exact Or.inl (key 2 (Or.inl h))
    · exact Or.inl (key 2 (Or.inr h))
    · exact Or.inr (key 3 (Or.inl h))
    · exact Or.inr (key 3 (Or.inr h))

end GroupG

section Action

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

def xy {W : WeierstrassCurve K} : W.toAffine.Point → Option (K × K)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve K} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

def act (γ : Γ K) : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point :=
  (castPt ((mem_Γ_iff _).1 γ.2)).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ.1 (E₀ K).toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ.1 (E₀ K).toAffine }

theorem act_apply (γ : Γ K) (P : (E₀ K).toAffine.Point) :
    act γ P = castPt ((mem_Γ_iff _).1 γ.2) (Point.vcInvFun γ.1 (E₀ K).toAffine P) := rfl

theorem heq_act (γ : Γ K) (P : (E₀ K).toAffine.Point) :
    HEq (Point.vcInvFun γ.1 (E₀ K).toAffine P) (act γ P) :=
  heq_castPt _ _

theorem xy_act (γ : Γ K) (P : (E₀ K).toAffine.Point) :
    xy (act γ P) = (xy P).map (fun q => (vcXInv γ.1 q.1, vcYInv γ.1 q.1 q.2)) := by
  rw [act_apply, xy_castPt, xy_vcInvFun]

theorem act_injective (γ : Γ K) : Function.Injective (act γ) := by
  intro P Q h
  have h' := congrArg xy h
  rw [xy_act, xy_act] at h'
  have hinj : Function.Injective (fun q : K × K => (vcXInv γ.1 q.1, vcYInv γ.1 q.1 q.2)) := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨hx, hy⟩ := hq
    have hx' : x = x' := by simpa using congrArg (vcX γ.1) hx
    subst hx'
    have hy' : y = y' := by simpa using congrArg (vcY γ.1 (vcXInv γ.1 x)) hy
    exact Prod.ext rfl hy'
  exact xy_injective (Option.map_injective hinj h')

theorem act_one (P : (E₀ K).toAffine.Point) : act (1 : Γ K) P = P := by
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (1 : VariableChange K) x, vcYInv (1 : VariableChange K) x y) = some (x, y)
    simp [vcXInv, vcYInv]

theorem act_mul (γ γ' : Γ K) (P : (E₀ K).toAffine.Point) : act (γ * γ') P = act γ (act γ' P) := by
  apply xy_injective
  rw [xy_act, xy_act, xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (γ.1 * γ'.1) x, vcYInv (γ.1 * γ'.1) x y) =
      some (vcXInv γ.1 (vcXInv γ'.1 x), vcYInv γ.1 (vcXInv γ'.1 x) (vcYInv γ'.1 x y))
    have hu : (γ.1.u : K) ≠ 0 := γ.1.u.ne_zero
    have hu' : (γ'.1.u : K) ≠ 0 := γ'.1.u.ne_zero
    simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · field_simp; ring
    · field_simp; ring

scoped instance actMulAction : MulAction (Γ K) (E₀ K).toAffine.Point where
  smul γ P := act γ P
  one_smul := act_one
  mul_smul := act_mul

theorem smul_pt_def (γ : Γ K) (P : (E₀ K).toAffine.Point) : γ • P = act γ P := rfl

scoped instance actDistrib : DistribMulAction (Γ K) (E₀ K).toAffine.Point where
  smul_zero γ := (act γ).map_zero
  smul_add γ := (act γ).map_add

theorem εΓ_smul_pt (P : (E₀ K).toAffine.Point) : (εΓ : Γ K) • P = -P := by
  rw [smul_pt_def]
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]
    show some (vcXInv (ε : VariableChange K) x, vcYInv (ε : VariableChange K) x y) =
      some (x, (E₀ K).toAffine.negY x y)
    simp only [vcXInv, vcYInv, ε_u, ε_r, ε_s, ε_t, inv_one, Units.val_one, one_pow, one_mul, sub_zero,
      zero_mul, WeierstrassCurve.Affine.negY, Option.some.injEq, Prod.mk.injEq, true_and]
    show y - 1 = -y - (E₀ K).a₁ * x - (E₀ K).a₃
    rw [E₀_a₁, E₀_a₃, neg_eq]; ring

open Pointwise

variable (K) in

private abbrev _root_.P2MKcCEN2.X (N : ℕ) : Type _ :=
  {H : AddSubgroup (E₀ K).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

p2m_export "P2MKcCEN2" "X"
theorem coe_smul_addSubgroup (γ : Γ K) (H : AddSubgroup (E₀ K).toAffine.Point) :
    ((γ • H : AddSubgroup (E₀ K).toAffine.Point) : Set (E₀ K).toAffine.Point) = act γ '' H := by
  rw [AddSubgroup.coe_pointwise_smul]; rfl

theorem smul_addSubgroup_eq_map (γ : Γ K) (H : AddSubgroup (E₀ K).toAffine.Point) :
    γ • H = H.map (act γ) := by
  apply SetLike.coe_injective
  rw [coe_smul_addSubgroup, AddSubgroup.coe_map]

theorem mem_smul_addSubgroup_iff (γ : Γ K) (H : AddSubgroup (E₀ K).toAffine.Point)
    (P : (E₀ K).toAffine.Point) : P ∈ γ • H ↔ ∃ Q ∈ H, act γ Q = P := by
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]; rfl

theorem isAddCyclic_smul (γ : Γ K) {H : AddSubgroup (E₀ K).toAffine.Point} (h : IsAddCyclic H) :
    IsAddCyclic (γ • H : AddSubgroup (E₀ K).toAffine.Point) := by
  rw [smul_addSubgroup_eq_map]
  exact isAddCyclic_of_surjective (H.equivMapOfInjective (act γ) (act_injective γ)).toAddMonoidHom
    (H.equivMapOfInjective (act γ) (act_injective γ)).surjective

theorem natCard_smul (γ : Γ K) (H : AddSubgroup (E₀ K).toAffine.Point) :
    Nat.card (γ • H : AddSubgroup (E₀ K).toAffine.Point) = Nat.card H := by
  rw [smul_addSubgroup_eq_map]
  exact AddSubgroup.card_map_of_injective (act_injective γ)

scoped instance XMulAction (N : ℕ) : MulAction (Γ K) (X K N) where
  smul γ H := ⟨γ • H.1, isAddCyclic_smul γ H.2.1, (natCard_smul γ H.1).trans H.2.2⟩
  one_smul H := Subtype.ext (one_smul _ H.1)
  mul_smul γ γ' H := Subtype.ext (mul_smul γ γ' H.1)

theorem coe_smul_X {N : ℕ} (γ : Γ K) (H : X K N) : ((γ • H : X K N) : AddSubgroup _) = γ • H.1 := rfl

theorem εΓ_smul_X {N : ℕ} (H : X K N) : (εΓ : Γ K) • H = H := by
  apply Subtype.ext
  rw [coe_smul_X]
  ext P
  rw [mem_smul_addSubgroup_iff]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rw [← smul_pt_def, εΓ_smul_pt]; exact H.1.neg_mem hQ
  · intro hP
    exact ⟨-P, H.1.neg_mem hP, by rw [← smul_pt_def, εΓ_smul_pt, neg_neg]⟩

theorem forall_exists_heq_iff {N : ℕ} [NeZero N] (γ : Γ K) (H H' : X K N) :
    (∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ.1 (E₀ K).toAffine T) T') ↔ γ • H = H' := by
  constructor
  · intro h
    apply Subtype.ext
    rw [coe_smul_X]
    haveI : Finite H'.1 := Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
    apply AddSubgroup.eq_of_le_of_card_ge
    · intro P hP
      rw [mem_smul_addSubgroup_iff] at hP
      obtain ⟨Q, hQ, rfl⟩ := hP
      obtain ⟨T', hT', hh⟩ := h Q hQ
      have : act γ Q = T' := eq_of_heq ((heq_act γ Q).symm.trans hh)
      rw [this]; exact hT'
    · rw [natCard_smul, H.2.2, H'.2.2]
  · rintro rfl T hT
    exact ⟨act γ T, (mem_smul_addSubgroup_iff γ H.1 _).2 ⟨T, hT, rfl⟩, heq_act γ T⟩

theorem exists_variableChange_iff_mem_orbit {N : ℕ} [NeZero N] (H H' : X K N) :
    (∃ γ : VariableChange K, γ • E₀ K = E₀ K ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (E₀ K).toAffine T) T') ↔
    H' ∈ MulAction.orbit (Γ K) H := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    have := (forall_exists_heq_iff (⟨γ, (mem_Γ_iff γ).2 hγ⟩ : Γ K) H H').1 h
    exact ⟨⟨γ, (mem_Γ_iff γ).2 hγ⟩, this⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, (mem_Γ_iff _).1 γ.2, (forall_exists_heq_iff γ H (γ • H)).2 rfl⟩

theorem Zε_le_ker (N : ℕ) : Zε K ≤ (MulAction.toPermHom (Γ K) (X K N)).ker := by
  rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
  ext H
  simp [εΓ_smul_X]

scoped instance GMulAction (N : ℕ) : MulAction (G K) (X K N) :=
  MulAction.compHom (X K N) (QuotientGroup.lift (Zε K) (MulAction.toPermHom (Γ K) (X K N)) (Zε_le_ker N))

theorem mk_smul_X {N : ℕ} (γ : Γ K) (H : X K N) : (QuotientGroup.mk γ : G K) • H = γ • H := by
  rw [MulAction.compHom_smul_def, QuotientGroup.lift_mk]; rfl

theorem orbit_G_eq {N : ℕ} (H : X K N) : MulAction.orbit (G K) H = MulAction.orbit (Γ K) H := by
  ext H'
  constructor
  · rintro ⟨g, rfl⟩
    induction g using QuotientGroup.induction_on with
    | H γ => exact ⟨γ, (mk_smul_X γ H).symm⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨(QuotientGroup.mk γ : G K), mk_smul_X γ H⟩

theorem mem_fixedBy_mk_iff {N : ℕ} (γ : Γ K) (H : X K N) :
    H ∈ MulAction.fixedBy (X K N) (QuotientGroup.mk γ : G K) ↔ γ • H = H := by
  rw [MulAction.mem_fixedBy, mk_smul_X]

end Action

section Census

open Pointwise MulAction AlgebraicCurve ModularCurve

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
variable {N : ℕ} [NeZero N]
variable {F : Type*} [Field F] [Algebra K F]

def αΓ : Γ K := ⟨αv ω, (mem_Γ_iff _).2 (αv_smul ω hω)⟩

def βΓ : Γ K := ⟨βv (Units.mk0 ω (omega_ne_zero ω hω)), (mem_Γ_iff _).2
  (βv_smul _ (by simpa using omega_pow_three ω hω))⟩

theorem mk_αΓ_ne_one : (QuotientGroup.mk (αΓ ω hω) : G K) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, mem_Zε_iff, not_or]
  exact ⟨αv_ne_one ω hω, αv_ne_ε ω hω⟩

theorem mk_αΓ_sq : (QuotientGroup.mk (αΓ ω hω) : G K) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_Zε_iff]
  right; exact αv_sq ω hω

theorem mk_βΓ_ne_one : (QuotientGroup.mk (βΓ ω hω) : G K) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, mem_Zε_iff, not_or]
  exact ⟨βv_ne_one _ (by simpa using omega_ne_one ω hω), βv_ne_ε _ (by simpa using omega_ne_one ω hω)⟩

theorem mk_βΓ_pow_three : (QuotientGroup.mk (βΓ ω hω) : G K) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_Zε_iff]
  left; exact βv_pow_three _ (by simpa using omega_pow_three ω hω)

theorem natCard_fixedBy_orbit (γ : Γ K) (H : X K N) :
    Nat.card (fixedBy (orbit (G K) H) (QuotientGroup.mk γ : G K)) =
      Nat.card {H' : X K N // H' ∈ orbit (G K) H ∧ γ • H' = H'} := by
  refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun H' => H' ∈ orbit (G K) H) (fun H' => γ • H' = H')))
  intro x
  rw [mem_fixedBy, Subtype.ext_iff, orbit.coe_smul, mk_smul_X]

include hω in

theorem census_core (j : F) (S : Finset (Place K F)) (f : X K N → Place K F)
    (hf1 : ∀ H, f H ∈ S) (hf2 : ∀ P ∈ S, ∃ H, f H = P)
    (hf3 : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • E₀ K = E₀ K ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (E₀ K).toAffine T) T')
    (hf4 : ∀ H, (f H).ord j = (Nat.card {H' : X K N // f H' = f H} : ℤ))
    (hA₂ : Nat.card {H : X K N // αΓ ω hω • H = H} = nuTwo N)
    (hA₃ : Nat.card {H : X K N // βΓ ω hω • H = H} = nuThree N) :
    (∀ P ∈ S, P.ord j = 1 ∨ P.ord j = 3 ∨ P.ord j = 4 ∨ P.ord j = 6 ∨ P.ord j = 12) ∧
    (S.filter fun P => P.ord j = 1).card + 3 * (S.filter fun P => P.ord j = 3).card +
      2 * (S.filter fun P => P.ord j = 6).card = nuTwo N ∧
    (S.filter fun P => P.ord j = 1).card + (S.filter fun P => P.ord j = 4).card = nuThree N := by
  haveI : Finite (Γ K) := finite_Γ' ω hω
  haveI : Finite (G K) := finite_G ω hω

  have horb : ∀ H H' : X K N, f H = f H' ↔ H' ∈ orbit (Γ K) H := fun H H' =>
    (hf3 H H').trans (exists_variableChange_iff_mem_orbit H H')
  have he : ∀ H : X K N, (f H).ord j = (Nat.card (orbit (G K) H) : ℤ) := by
    intro H
    rw [hf4]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun H' => by
      rw [eq_comm, horb, ← orbit_G_eq])

  have hfin : ∀ P : Place K F, {H : X K N | f H = P}.Finite := by
    intro P
    by_cases hP : ∃ H₀, f H₀ = P
    · obtain ⟨H₀, rfl⟩ := hP
      have : {H : X K N | f H = f H₀} = orbit (Γ K) H₀ := by
        ext H'
        rw [Set.mem_setOf_eq, eq_comm]
        exact horb H₀ H'
      rw [this]
      exact Set.finite_range _
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro H rfl
      exact hP ⟨H, rfl⟩
  haveI : Finite (X K N) := by
    rw [← Set.finite_univ_iff]
    refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun P _ => hfin P) ?_
    intro H _
    exact Set.mem_biUnion (hf1 H) rfl
  letI : Fintype (X K N) := Fintype.ofFinite _

  have hM : ∀ H : X K N, _ := fun H =>
    haveI : Nonempty (orbit (G K) H) := ⟨⟨H, mem_orbit_self H⟩⟩
    MulAction.natCard_fixedBy_of_isPretransitive_of_card_eq_twelve (natCard_G ω hω) G_sq_or_cube
      (orbit (G K) H)

  have h1 : ∀ P ∈ S, P.ord j = 1 ∨ P.ord j = 3 ∨ P.ord j = 4 ∨ P.ord j = 6 ∨ P.ord j = 12 := by
    intro P hP
    obtain ⟨H, rfl⟩ := hf2 P hP
    rw [he H]
    rcases (hM H).1 with h | h | h | h | h <;> rw [h] <;> norm_num

  have hsum : ∀ (γ : Γ K) (μ : ℤ → ℕ),
      (∀ H : X K N, Nat.card {H' : X K N // H' ∈ orbit (G K) H ∧ γ • H' = H'} = μ ((f H).ord j)) →
      ∑ P ∈ S, μ (P.ord j) = Nat.card {H : X K N // γ • H = H} := by
    intro γ μ hμ
    classical
    have hRHS : Nat.card {H : X K N // γ • H = H} = (Finset.univ.filter fun H : X K N => γ • H = H).card :=
      Nat.subtype_card _ (fun H => by simp)
    rw [hRHS, Finset.card_eq_sum_card_fiberwise (t := S) (f := f) (fun H _ => hf1 H)]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨H₀, rfl⟩ := hf2 P hP
    rw [← hμ H₀]
    refine Nat.subtype_card _ fun H' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [orbit_G_eq, ← horb, eq_comm]
    tauto

  have h2 : ∑ P ∈ S, ((if P.ord j = 1 then 1 else 0) + (if P.ord j = 3 then 3 else 0) +
      (if P.ord j = 6 then 2 else 0)) = nuTwo N := by
    rw [← hA₂]
    apply hsum (αΓ ω hω) (fun e => (if e = 1 then 1 else 0) + (if e = 3 then 3 else 0) +
      (if e = 6 then 2 else 0))
    intro H
    rw [← natCard_fixedBy_orbit, he H]
    obtain ⟨hsize, hinv, -⟩ := hM H
    obtain ⟨c1, c3, c4, c6, c12⟩ := hinv _ (mk_αΓ_ne_one ω hω) (mk_αΓ_sq ω hω)
    rcases hsize with h | h | h | h | h
    · rw [c1 h, h]; norm_num
    · rw [c3 h, h]; norm_num
    · rw [c4 h, h]; norm_num
    · rw [c6 h, h]; norm_num
    · rw [c12 h, h]; norm_num

  have h3 : ∑ P ∈ S, ((if P.ord j = 1 then 1 else 0) + (if P.ord j = 4 then 1 else 0)) = nuThree N := by
    rw [← hA₃]
    apply hsum (βΓ ω hω) (fun e => (if e = 1 then 1 else 0) + (if e = 4 then 1 else 0))
    intro H
    rw [← natCard_fixedBy_orbit, he H]
    obtain ⟨hsize, -, hord⟩ := hM H
    obtain ⟨c1, c3, c4, c6, c12⟩ := hord _ (mk_βΓ_ne_one ω hω) (mk_βΓ_pow_three ω hω)
    rcases hsize with h | h | h | h | h
    · rw [c1 h, h]; norm_num
    · rw [c3 h, h]; norm_num
    · rw [c4 h, h]; norm_num
    · rw [c6 h, h]; norm_num
    · rw [c12 h, h]; norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [← h2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter,
      Finset.card_filter, Finset.mul_sum, Finset.mul_sum]
    congr 1; congr 1
    · exact Finset.sum_congr rfl fun P _ => by split_ifs <;> rfl
    · exact Finset.sum_congr rfl fun P _ => by split_ifs <;> rfl
  · rw [← h3, Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]

theorem natCard_fixed_X_eq (γ : Γ K) :
    Nat.card {H : X K N // γ • H = H} =
      Nat.card {H : AddSubgroup (E₀ K).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ.1 (E₀ K).toAffine T) T'} := by
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun H => (forall_exists_heq_iff γ H H).symm).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter
      (fun H : AddSubgroup (E₀ K).toAffine.Point => IsAddCyclic H ∧ Nat.card H = N)
      (fun H : AddSubgroup (E₀ K).toAffine.Point =>
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ.1 (E₀ K).toAffine T) T')).trans
      (Equiv.subtypeEquivRight fun H => and_assoc)))

end Census

section Main

open AlgebraicCurve ModularCurve

theorem exists_omega (K : Type*) [Field K] [IsAlgClosed K] : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K)
    (by
      have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).degree = 2 := by compute_degree!
      rw [this]; norm_num)
  exact ⟨ω, by simpa using hω⟩

theorem census (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)) :
    (∀ P ∈ S, P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 4 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 12) ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      3 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3).card +
      2 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6).card =
      nuTwo N ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 4).card =
      nuThree N := by
  classical
  obtain ⟨ω, hω⟩ := exists_omega K
  set j : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩ with hj

  have hS' : ∀ P, P ∈ S ↔ 0 < P.ord (j - algebraMap K (modularFunctionFieldFullC K N) 0) := by
    intro P; rw [map_zero, sub_zero]; exact hS P
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
    ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC K N hN 0 (E₀ K)
      (E₀_j K) S hS'
  simp only [map_zero, sub_zero] at hf4
  have hA₂ : Nat.card {H : X K N // αΓ ω hω • H = H} = nuTwo N := by
    rw [natCard_fixed_X_eq]
    exact WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
      ω hω N hN
  have hA₃ : Nat.card {H : X K N // βΓ ω hω • H = H} = nuThree N := by
    rw [natCard_fixed_X_eq]
    exact WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuThree_of_char_two
      (Units.mk0 ω (omega_ne_zero ω hω)) (by simpa using omega_pow_three ω hω)
      (by simpa using omega_ne_one ω hω) N hN
  exact census_core ω hω j S f hf1 hf2 hf3 hf4 hA₂ hA₃

end Main

end P2MKcCEN2
p2m_reactivate "P2MW.S_ModularCurve_ord_jqModC_census_of_char_two.P2MKcCEN2"

open AlgebraicCurve ModularCurve in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)) :
    (∀ P ∈ S, P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 4 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 12) ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      3 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3).card +
      2 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6).card =
      nuTwo N ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 4).card =
      nuThree N :=
  P2MKcCEN2.census K N hN S hS

end S_ModularCurve_ord_jqModC_census_of_char_two
end P2MW
export P2MW.S_ModularCurve_ord_jqModC_census_of_char_two (solution)
