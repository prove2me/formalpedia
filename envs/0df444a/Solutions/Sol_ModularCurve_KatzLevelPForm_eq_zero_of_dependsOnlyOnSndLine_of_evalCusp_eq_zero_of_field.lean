-- Prove2me | solution 1 for ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/39cb191f-bb81-51b2-bbcf-571d8f035107

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_WeierstrassCurve_Generic
import Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero
import Theorems.Thm_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
import Theorems.Thm_ModularCurve_algebraicIndependent_variableChange_tateLaurent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

universe u

noncomputable section

p2m_open "Polynomial WeierstrassCurve~cusp"

namespace ModularCurve
p2m_export "ModularCurve" "tateLaurent qExpand qExpand_C qExpand_injective indepElt indepElt_map LevelPData LevelPData.map LevelPData.map_xP LevelPData.map_xQ LevelPData.variableChange_xP LevelPData.variableChange_xQ IsLevelPStructure KatzLevelPForm cuspData algebraMap_laurentSeries_apply isUnit_Δ_tateBase tateBase KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero algebraicIndependent_variableChange_tateLaurent"
namespace QExpFieldProof
namespace VC
p2m_open "ModularCurve"

variable {R : Type*} [CommRing R]

def wt (n : ℕ) : ℕ := n ^ 2 - if Even n then 4 else 1

theorem wt_of_odd (n j : ℕ) (h : n = 2 * j + 1) : wt n = 4 * j * (j + 1) := by
  subst h
  have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
  have hsq : (2 * j + 1) ^ 2 = 4 * j * (j + 1) + 1 := by ring
  rw [wt, if_neg hodd, hsq]; omega

theorem wt_of_even (n j : ℕ) (h : n = 2 * j + 2) : wt n = 4 * j * (j + 2) := by
  subst h
  have hev : Even (2 * j + 2) := ⟨j + 1, by ring⟩
  have hsq : (2 * j + 2) ^ 2 = 4 * j * (j + 2) + 4 := by ring
  rw [wt, if_pos hev, hsq]; omega

theorem preNormEDS'_scale (l b c d : R) (n : ℕ) :
    preNormEDS' (l ^ 12 * b) (l ^ 8 * c) (l ^ 12 * d) n = l ^ wt n * preNormEDS' b c d n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp [wt]
  | two => simp [wt]
  | three => rw [preNormEDS'_three, preNormEDS'_three, wt_of_odd 3 1 rfl]
  | four => rw [preNormEDS'_four, preNormEDS'_four, wt_of_even 4 1 rfl]
  | even m ih =>
    rw [preNormEDS'_even, preNormEDS'_even, ih (m + 1) (by omega), ih (m + 2) (by omega),
      ih (m + 3) (by omega), ih (m + 4) (by omega), ih (m + 5) (by omega)]
    rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [wt_of_odd (j + j + 1) j (by ring), wt_of_even (j + j + 2) j (by ring),
        wt_of_odd (j + j + 3) (j + 1) (by ring), wt_of_even (j + j + 4) (j + 1) (by ring),
        wt_of_odd (j + j + 5) (j + 2) (by ring), wt_of_even (2 * (j + j + 3)) (2 * j + 2) (by ring)]
      ring
    · rw [wt_of_even (2 * j + 1 + 1) j (by ring), wt_of_odd (2 * j + 1 + 2) (j + 1) (by ring),
        wt_of_even (2 * j + 1 + 3) (j + 1) (by ring), wt_of_odd (2 * j + 1 + 4) (j + 2) (by ring),
        wt_of_even (2 * j + 1 + 5) (j + 2) (by ring),
        wt_of_even (2 * (2 * j + 1 + 3)) (2 * j + 3) (by ring)]
      ring
  | odd m ih =>
    rw [preNormEDS'_odd, preNormEDS'_odd, ih (m + 1) (by omega), ih (m + 2) (by omega),
      ih (m + 3) (by omega), ih (m + 4) (by omega)]
    rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hev : Even (j + j) := ⟨j, rfl⟩
      rw [if_pos hev, if_pos hev, if_pos hev, if_pos hev,
        wt_of_odd (j + j + 1) j (by ring), wt_of_even (j + j + 2) j (by ring),
        wt_of_odd (j + j + 3) (j + 1) (by ring), wt_of_even (j + j + 4) (j + 1) (by ring),
        wt_of_odd (2 * (j + j + 2) + 1) (2 * j + 2) (by ring)]
      ring
    · have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
      rw [if_neg hodd, if_neg hodd, if_neg hodd, if_neg hodd,
        wt_of_even (2 * j + 1 + 1) j (by ring), wt_of_odd (2 * j + 1 + 2) (j + 1) (by ring),
        wt_of_even (2 * j + 1 + 3) (j + 1) (by ring), wt_of_odd (2 * j + 1 + 4) (j + 2) (by ring),
        wt_of_odd (2 * (2 * j + 1 + 2) + 1) (2 * j + 3) (by ring)]
      ring

section

variable (W : WeierstrassCurve R) (C : VariableChange R) (x : R)

theorem eval_Ψ₂Sq_variableChange :
    ((C • W).Ψ₂Sq).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ 6 * W.Ψ₂Sq.eval x := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_C, eval_pow, eval_X, variableChange_b₂,
    variableChange_b₄, variableChange_b₆]
  ring1

theorem eval_Ψ₃_variableChange :
    ((C • W).Ψ₃).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ 8 * W.Ψ₃.eval x := by
  simp only [Ψ₃, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_ofNat, variableChange_b₂,
    variableChange_b₄, variableChange_b₆, variableChange_b₈]
  ring1

theorem eval_preΨ₄_variableChange :
    ((C • W).preΨ₄).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ 12 * W.preΨ₄.eval x := by
  simp only [preΨ₄, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_ofNat,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, variableChange_b₈]
  linear_combination (-(2 * x * C.r - C.r ^ 2) * ((C.u⁻¹ : Rˣ) : R) ^ 12) * W.b_relation

theorem eval_preΨ'_variableChange (n : ℕ) :
    ((C • W).preΨ' n).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ wt n * (W.preΨ' n).eval x := by
  have hB : ((C • W).Ψ₂Sq ^ 2).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ 12 * (W.Ψ₂Sq ^ 2).eval x := by
    rw [eval_pow, eval_pow, eval_Ψ₂Sq_variableChange]; ring
  rw [preΨ', ← coe_evalRingHom, map_preNormEDS', coe_evalRingHom, hB, eval_Ψ₃_variableChange,
    eval_preΨ₄_variableChange, preNormEDS'_scale, preΨ', ← coe_evalRingHom, map_preNormEDS']

theorem eval_preΨ_variableChange_nat (n : ℕ) :
    ((C • W).preΨ n).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ wt n * (W.preΨ n).eval x := by
  rw [preΨ_ofNat, preΨ_ofNat]
  exact eval_preΨ'_variableChange W C x n

theorem eval_ΨSq_variableChange_nat (m : ℕ) :
    ((C • W).ΨSq m).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (m ^ 2 - 1)) * (W.ΨSq m).eval x := by
  have hP := eval_preΨ'_variableChange W C x m
  rw [ΨSq_ofNat, ΨSq_ofNat, eval_mul, eval_mul, eval_pow, eval_pow, hP]
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hev : Even (j + j) := ⟨j, rfl⟩
    simp only [if_pos hev]
    rw [eval_Ψ₂Sq_variableChange]
    rcases j with _ | j
    · simp
    · rw [wt_of_even (j + 1 + (j + 1)) j (by ring)]
      have h2 : 2 * ((j + 1 + (j + 1)) ^ 2 - 1) = 8 * (j * (j + 2)) + 6 := by
        have : (j + 1 + (j + 1)) ^ 2 = 4 * (j * (j + 2)) + 4 := by ring
        omega
      rw [h2]; ring
  · have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
    simp only [if_neg hodd, eval_one]
    rw [wt_of_odd (2 * j + 1) j rfl]
    have h1 : 2 * ((2 * j + 1) ^ 2 - 1) = 8 * (j * (j + 1)) := by
      have : (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 := by ring
      omega
    rw [h1]; ring

theorem eval_preΨ'_odd (j : ℕ) :
    ((C • W).preΨ' (2 * j + 1)).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ (4 * (j * (j + 1))) * (W.preΨ' (2 * j + 1)).eval x := by
  rw [eval_preΨ'_variableChange, wt_of_odd (2 * j + 1) j rfl, Nat.mul_assoc]

theorem eval_preΨ'_even (j : ℕ) :
    ((C • W).preΨ' (2 * j + 2)).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ (4 * (j * (j + 2))) * (W.preΨ' (2 * j + 2)).eval x := by
  rw [eval_preΨ'_variableChange, wt_of_even (2 * j + 2) j rfl, Nat.mul_assoc]

theorem eval_Φ_variableChange_succ (k : ℕ) :
    ((C • W).Φ ((k : ℤ) + 1)).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (k + 1) ^ 2) *
        ((W.Φ ((k : ℤ) + 1)).eval x - C.r * (W.ΨSq ((k : ℤ) + 1)).eval x) := by
  have hΨSq : W.ΨSq ((k : ℤ) + 1) = W.preΨ' (k + 1) ^ 2 * if Even k then 1 else W.Ψ₂Sq := by
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, ΨSq_ofNat]
    by_cases hk : Even k
    · have hk' : ¬ Even (k + 1) := fun h => Nat.even_add_one.mp h hk
      rw [if_pos hk, if_neg hk']
    · have hk' : Even (k + 1) := Nat.even_add_one.mpr hk
      rw [if_neg hk, if_pos hk']
  rw [Φ_ofNat, Φ_ofNat, hΨSq]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, apply_ite (eval _), eval_one]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hev : Even (j + j) := ⟨j, rfl⟩
    simp only [if_pos hev]
    rw [eval_Ψ₂Sq_variableChange, show j + j + 1 = 2 * j + 1 by ring, eval_preΨ'_odd,
      show j + j + 2 = 2 * j + 2 by ring, eval_preΨ'_even]
    rcases j with _ | j
    · simp only [mul_zero, zero_add, preΨ'_zero, eval_zero]
      ring
    · rw [show j + 1 + (j + 1) = 2 * j + 2 by ring, eval_preΨ'_even]
      ring
  · have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
    simp only [if_neg hodd]
    rw [eval_Ψ₂Sq_variableChange, show 2 * j + 1 + 1 = 2 * j + 2 by ring, eval_preΨ'_even,
      show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring, eval_preΨ'_odd, eval_preΨ'_odd]
    ring

theorem eval_Φ_variableChange_nat (m : ℕ) :
    ((C • W).Φ m).eval ((C.u⁻¹ : Rˣ) ^ 2 * (x - C.r) : R) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * m ^ 2) * ((W.Φ m).eval x - C.r * (W.ΨSq m).eval x) := by
  rcases m with _ | k
  · simp
  · have h := eval_Φ_variableChange_succ W C x k
    push_cast at h ⊢
    exact h

end

variable {A : Type u} [CommRing A] (W : WeierstrassCurve A) (C : VariableChange A) (p : ℕ)

theorem indepFactor_variableChange (a : ℕ) (ha : 1 ≤ a) (x₀ x : A) :
    ((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r) * ((C • W).ΨSq a).eval (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x₀ - C.r)) -
        ((C • W).Φ a).eval (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x₀ - C.r)) =
      ((C.u⁻¹ : Aˣ) : A) ^ (2 * a ^ 2) * (x * (W.ΨSq a).eval x₀ - (W.Φ a).eval x₀) := by
  rw [eval_ΨSq_variableChange_nat, eval_Φ_variableChange_nat]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have h1 : 2 * ((1 + b) ^ 2 - 1) = 2 * (b * (b + 2)) := by
    have : (1 + b) ^ 2 = b * (b + 2) + 1 := by ring
    omega
  have h2 : 2 * (1 + b) ^ 2 = 2 * (b * (b + 2)) + 2 := by ring
  rw [h1, h2]
  ring

theorem indepElt_variableChange (x₀ x : A) :
    indepElt (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x₀ - C.r)) (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      (∏ a ∈ Finset.Icc 1 ((p - 1) / 2), ((C.u⁻¹ : Aˣ) : A) ^ (2 * a ^ 2)) *
        indepElt W p x₀ x := by
  rw [indepElt, indepElt, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  exact indepFactor_variableChange W C a (Finset.mem_Icc.mp ha).1 x₀ x

theorem isUnit_indepElt_variableChange {x₀ x : A} (h : IsUnit (indepElt W p x₀ x)) :
    IsUnit (indepElt (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x₀ - C.r))
      (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r))) := by
  rw [indepElt_variableChange]
  refine IsUnit.mul ?_ h
  rw [Finset.prod_pow_eq_pow_sum]
  exact (Units.isUnit _).pow _

theorem isLevelPStructure_variableChange {D : LevelPData A} (h : IsLevelPStructure W p D) :
    IsLevelPStructure (C • W) p (D.variableChange C) where
  equation_P := h.equation_P_variableChange C
  equation_Q := h.equation_Q_variableChange C
  preΨ_P := by
    rw [LevelPData.variableChange_xP, eval_preΨ_variableChange_nat, h.preΨ_P, mul_zero]
  preΨ_Q := by
    rw [LevelPData.variableChange_xQ, eval_preΨ_variableChange_nat, h.preΨ_Q, mul_zero]
  isUnit_indepElt_PQ := by
    rw [LevelPData.variableChange_xP, LevelPData.variableChange_xQ]
    exact isUnit_indepElt_variableChange W C p h.isUnit_indepElt_PQ
  isUnit_indepElt_QP := by
    rw [LevelPData.variableChange_xP, LevelPData.variableChange_xQ]
    exact isUnit_indepElt_variableChange W C p h.isUnit_indepElt_QP

end ModularCurve.QExpFieldProof.VC

namespace ModularCurve
p2m_export "ModularCurve" "tateLaurent qExpand qExpand_C qExpand_injective indepElt indepElt_map LevelPData LevelPData.map LevelPData.map_xP LevelPData.map_xQ LevelPData.variableChange_xP LevelPData.variableChange_xQ IsLevelPStructure KatzLevelPForm cuspData algebraMap_laurentSeries_apply isUnit_Δ_tateBase tateBase KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero algebraicIndependent_variableChange_tateLaurent"
namespace QExpFieldProof
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve"

section Forms

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ}

theorem toFun_congr (G : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
    {W W' : WeierstrassCurve A} (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) {D D' : LevelPData A}
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W' p D') (e : W = W') (e' : D = D') :
    G.toFun W hW D hD = G.toFun W' hW' D' hD' := by
  subst e e'
  rfl

theorem map_toFun' (G : KatzLevelPForm R p k) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    f (G.toFun W hW D hD) = G.toFun (W.map (f : A →+* B)) (KatzModularForm.isUnit_Δ_map _ hW)
      (D.map (f : A →+* B)) (hD.map _) :=
  (G.map_toFun f W hW _ D hD _).symm

variable {K : Type u} [Field K]

theorem isLevelPStructure_map_algEquiv
    (σ : Generic.Closure K ≃ₐ[Generic.FunctionField K] Generic.Closure K)
    {D : LevelPData (Generic.Closure K)} (hD : IsLevelPStructure (Generic.curve K) p D) :
    IsLevelPStructure (Generic.curve K) p
      (D.map (σ : Generic.Closure K →+* Generic.Closure K)) := by
  have h := hD.map (σ : Generic.Closure K →+* Generic.Closure K)
  rwa [Generic.curve_map_algEquiv K σ] at h

theorem toFun_map_algEquiv (G : KatzLevelPForm K p k)
    (σ : Generic.Closure K ≃ₐ[Generic.FunctionField K] Generic.Closure K)
    (D : LevelPData (Generic.Closure K)) (hD : IsLevelPStructure (Generic.curve K) p D)
    (hσD : IsLevelPStructure (Generic.curve K) p
      (D.map (σ : Generic.Closure K →+* Generic.Closure K))) :
    G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K)
        (D.map (σ : Generic.Closure K →+* Generic.Closure K)) hσD =
      σ (G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D hD) := by
  let τ : Generic.Closure K →ₐ[K] Generic.Closure K :=
    (σ : Generic.Closure K →ₐ[Generic.FunctionField K] Generic.Closure K).restrictScalars K
  have hτ : (τ : Generic.Closure K →+* Generic.Closure K) =
      (σ : Generic.Closure K →+* Generic.Closure K) := rfl
  have e : (Generic.curve K).map (τ : Generic.Closure K →+* Generic.Closure K) = Generic.curve K := by
    rw [hτ]
    exact Generic.curve_map_algEquiv K σ
  have h1 := map_toFun' G τ (Generic.curve K) (Generic.isUnit_Δ_curve K) D hD
  rw [toFun_congr G _ (Generic.isUnit_Δ_curve K) _ hσD e (by rw [hτ])] at h1
  exact h1.symm

end Forms

section Descent

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

theorem equation_algebraMap_iff (W : WeierstrassCurve L) (x y : L) :
    (W.map (algebraMap L M)).toAffine.Equation (algebraMap L M x) (algebraMap L M y) ↔
      W.toAffine.Equation x y := by
  refine ⟨fun h => ?_, fun h => h.map (algebraMap L M)⟩
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  apply (algebraMap L M).injective
  simpa [map_add, map_mul, map_pow] using h

theorem eval_map_ordinatePoly_eq_zero (W : WeierstrassCurve L) (x₀ : L) (y : M)
    (hy : (W.map (algebraMap L M)).toAffine.Equation (algebraMap L M x₀) y) :
    ((X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) * X -
        Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)).map (algebraMap L M)).eval y = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hy
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hy
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
    map_add, map_mul, map_pow]
  linear_combination hy

theorem ordinatePoly_ne_zero (W : WeierstrassCurve L) (x₀ : L) :
    (X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) * X -
      Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) : Polynomial L) ≠ 0 := by
  intro h
  have h2 := congrArg (fun q : Polynomial L => q.coeff 2) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, coeff_zero] at h2
  norm_num at h2

variable [IsAlgClosed L]

theorem mem_range_algebraMap_of_eval_map_eq_zero {f : Polynomial L} (hf : f ≠ 0) {x : M}
    (hx : (f.map (algebraMap L M)).eval x = 0) : x ∈ (algebraMap L M).range := by
  have hint : IsIntegral L x := by
    have halg : IsAlgebraic L x := ⟨f, hf, by rwa [aeval_def, eval₂_eq_eval_map]⟩
    exact halg.isIntegral
  exact hint.mem_range_algebraMap_of_minpoly_splits (K := L) (IsAlgClosed.splits _)

variable {p : ℕ}

theorem exists_levelPData_map_eq (hp : (p : L) ≠ 0) (W : WeierstrassCurve L) (D : LevelPData M)
    (hD : IsLevelPStructure (W.map (algebraMap L M)) p D) :
    ∃ D₀ : LevelPData L, IsLevelPStructure W p D₀ ∧ D₀.map (algebraMap L M) = D := by
  have hψ : W.preΨ p ≠ 0 := W.preΨ_ne_zero (by exact_mod_cast hp)
  obtain ⟨xP, hxP⟩ : D.xP ∈ (algebraMap L M).range := by
    refine mem_range_algebraMap_of_eval_map_eq_zero hψ ?_
    rw [← WeierstrassCurve.map_preΨ]; exact hD.preΨ_P
  obtain ⟨xQ, hxQ⟩ : D.xQ ∈ (algebraMap L M).range := by
    refine mem_range_algebraMap_of_eval_map_eq_zero hψ ?_
    rw [← WeierstrassCurve.map_preΨ]; exact hD.preΨ_Q
  obtain ⟨yP, hyP⟩ : D.yP ∈ (algebraMap L M).range := by
    refine mem_range_algebraMap_of_eval_map_eq_zero (ordinatePoly_ne_zero W xP)
      (eval_map_ordinatePoly_eq_zero W xP D.yP ?_)
    rw [hxP]; exact hD.equation_P
  obtain ⟨yQ, hyQ⟩ : D.yQ ∈ (algebraMap L M).range := by
    refine mem_range_algebraMap_of_eval_map_eq_zero (ordinatePoly_ne_zero W xQ)
      (eval_map_ordinatePoly_eq_zero W xQ D.yQ ?_)
    rw [hxQ]; exact hD.equation_Q
  have hDeq : (⟨xP, yP, xQ, yQ⟩ : LevelPData L).map (algebraMap L M) = D := by
    ext <;> simp [LevelPData.map, hxP, hyP, hxQ, hyQ]
  refine ⟨⟨xP, yP, xQ, yQ⟩, ?_, hDeq⟩
  have hinj := (algebraMap L M).injective
  have hD' : IsLevelPStructure (W.map (algebraMap L M)) p
      ((⟨xP, yP, xQ, yQ⟩ : LevelPData L).map (algebraMap L M)) := by rwa [hDeq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (equation_algebraMap_iff W xP yP).mp hD'.equation_P
  · exact (equation_algebraMap_iff W xQ yQ).mp hD'.equation_Q
  · apply hinj
    rw [map_zero, ← eval₂_at_apply, ← eval_map, ← WeierstrassCurve.map_preΨ]
    exact hD'.preΨ_P
  · apply hinj
    rw [map_zero, ← eval₂_at_apply, ← eval_map, ← WeierstrassCurve.map_preΨ]
    exact hD'.preΨ_Q
  · rw [isUnit_iff_ne_zero]
    intro h0
    have hu := hD'.isUnit_indepElt_PQ
    simp only [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map, h0, map_zero] at hu
    exact not_isUnit_zero hu
  · rw [isUnit_iff_ne_zero]
    intro h0
    have hu := hD'.isUnit_indepElt_QP
    simp only [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map, h0, map_zero] at hu
    exact not_isUnit_zero hu

end Descent

section Dominance

variable (K : Type u) [Field K] (p : ℕ)

@[nolint unusedArguments]
def Ω (K : Type u) [Field K] (_p : ℕ) : Type u :=
  FractionRing (MvPolynomial (Fin 4) (LaurentSeries K))

scoped instance instFieldΩ : Field (Ω K p) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin 4) (LaurentSeries K))))

scoped instance algPΩ : Algebra (MvPolynomial (Fin 4) (LaurentSeries K)) (Ω K p) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin 4) (LaurentSeries K))
    (FractionRing (MvPolynomial (Fin 4) (LaurentSeries K))))

scoped instance isFractionRingΩ : IsFractionRing (MvPolynomial (Fin 4) (LaurentSeries K)) (Ω K p) :=
  inferInstanceAs (IsFractionRing (MvPolynomial (Fin 4) (LaurentSeries K))
    (FractionRing (MvPolynomial (Fin 4) (LaurentSeries K))))

def ιP : MvPolynomial (Fin 4) (LaurentSeries K) →+* Ω K p :=
  algebraMap (MvPolynomial (Fin 4) (LaurentSeries K)) (Ω K p)

theorem ιP_injective : Function.Injective (ιP K p) :=
  IsFractionRing.injective (MvPolynomial (Fin 4) (LaurentSeries K)) (Ω K p)

def ι₀ : LaurentSeries K →+* Ω K p := (ιP K p).comp MvPolynomial.C

def jK : K →+* Ω K p := (ι₀ K p).comp (HahnSeries.C : K →+* LaurentSeries K)

scoped instance algK : Algebra K (Ω K p) := (jK K p).toAlgebra

theorem algebraMap_K_eq : algebraMap K (Ω K p) = jK K p := rfl

theorem algebraMap_K_laurent (r : K) : algebraMap K (LaurentSeries K) r = HahnSeries.C r := by
  rw [algebraMap_laurentSeries_apply K (R := K) r, Algebra.algebraMap_self, RingHom.id_apply]

def ι₀ₐ : LaurentSeries K →ₐ[K] Ω K p :=
  { ι₀ K p with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [algebraMap_K_laurent, algebraMap_K_eq]
      rfl }

@[scoped simp] theorem coe_ι₀ₐ : ((ι₀ₐ K p : LaurentSeries K →ₐ[K] Ω K p) : LaurentSeries K →+* Ω K p) = ι₀ K p :=
  RingHom.ext fun _ => rfl

def gen (i : Fin 4) : Ω K p := ιP K p (MvPolynomial.X i)

theorem gen_ne_zero (i : Fin 4) : gen K p i ≠ 0 := by
  rw [gen, Ne, map_eq_zero_iff _ (ιP_injective K p)]
  exact MvPolynomial.X_ne_zero i

def Cgen : VariableChange (Ω K p) :=
  ⟨Units.mk0 (gen K p 0) (gen_ne_zero K p 0), gen K p 1, gen K p 2, gen K p 3⟩

variable [NeZero p]

def ι₁ : LaurentSeries K →+* Ω K p := (ι₀ K p).comp (qExpand K p)

scoped instance algL : Algebra (LaurentSeries K) (Ω K p) := (ι₁ K p).toAlgebra

theorem algebraMap_L_eq : algebraMap (LaurentSeries K) (Ω K p) = ι₁ K p := rfl

theorem ι₁_C (r : K) : ι₁ K p (HahnSeries.C r) = jK K p r := by
  rw [ι₁, RingHom.comp_apply, qExpand_C]
  rfl

scoped instance towerKLΩ : IsScalarTower K (LaurentSeries K) (Ω K p) :=
  ⟨fun x y z => by
    simp only [Algebra.smul_def, algebraMap_L_eq, algebraMap_K_eq]
    rw [← HahnSeries.C_mul_eq_smul, map_mul, ι₁_C, mul_assoc]⟩

theorem towerKLΩ' :
    @IsScalarTower K (LaurentSeries K) (Ω K p) Algebra.toSMul (algL K p).toSMul (algK K p).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := LaurentSeries K) (A := Ω K p) fun r => by
    rw [algebraMap_K_eq, algebraMap_L_eq, algebraMap_K_laurent, ι₁_C]

theorem algebraicIndependent_Cgen :
    AlgebraicIndependent (LaurentSeries K)
      ![((Cgen K p).u : Ω K p), (Cgen K p).r, (Cgen K p).s, (Cgen K p).t] := by
  have key : ((MvPolynomial.aeval
        ![((Cgen K p).u : Ω K p), (Cgen K p).r, (Cgen K p).s, (Cgen K p).t] :
        MvPolynomial (Fin 4) (LaurentSeries K) →ₐ[LaurentSeries K] Ω K p) :
        MvPolynomial (Fin 4) (LaurentSeries K) →+* Ω K p) =
      (ιP K p).comp (MvPolynomial.map (qExpand K p)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [AlgHom.coe_toRingHom, MvPolynomial.algHom_C, algebraMap_L_eq, RingHom.comp_apply,
        MvPolynomial.map_C]
      rfl
    · rw [AlgHom.coe_toRingHom, MvPolynomial.aeval_X, RingHom.comp_apply, MvPolynomial.map_X]
      fin_cases i <;> rfl
  change Function.Injective (MvPolynomial.aeval _)
  rw [← AlgHom.coe_toRingHom, key, RingHom.coe_comp]
  exact (ιP_injective K p).comp (MvPolynomial.map_injective _ (qExpand_injective p))

def tateΩ : WeierstrassCurve (Ω K p) := (tateBase K p).map (ι₀ K p)

theorem tateΩ_eq : tateΩ K p = (tateLaurent K).map (algebraMap (LaurentSeries K) (Ω K p)) := by
  rw [tateΩ, tateBase, WeierstrassCurve.map_map]
  rfl

theorem isUnit_Δ_tateΩ : IsUnit (tateΩ K p).Δ :=
  KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_tateBase K p)

def E₁ : WeierstrassCurve (Ω K p) := Cgen K p • tateΩ K p

theorem isUnit_Δ_E₁ : IsUnit (E₁ K p).Δ := by
  rw [E₁, variableChange_Δ]
  exact ((Units.isUnit _).pow 12).mul (isUnit_Δ_tateΩ K p)

theorem classify_E₁_injective : Function.Injective (Generic.classify K (E₁ K p)) := by
  have h := ModularCurve.algebraicIndependent_variableChange_tateLaurent K (Ω K p) (Cgen K p)
    (algebraicIndependent_Cgen K p)
  rw [← tateΩ_eq] at h
  exact h

variable {K p}
variable {k : ℤ} (G : KatzLevelPForm K p k) (ζ : Kˣ)
  (hc : IsLevelPStructure (tateBase K p) p (cuspData K p ζ ![1, 0] ![0, 1]))

def D₀Ω : LevelPData (Ω K p) := (cuspData K p ζ ![1, 0] ![0, 1]).map (ι₀ K p)

include hc in
theorem isLevelPStructure_D₀Ω : IsLevelPStructure (tateΩ K p) p (D₀Ω ζ) := hc.map _

def D₁ : LevelPData (Ω K p) := (D₀Ω (p := p) ζ).variableChange (Cgen K p)

include hc in
theorem isLevelPStructure_D₁ : IsLevelPStructure (E₁ K p) p (D₁ (p := p) ζ) :=
  VC.isLevelPStructure_variableChange (tateΩ K p) (Cgen K p) p (isLevelPStructure_D₀Ω ζ hc)

theorem toFun_E₁_eq_zero
    (h0 : G.toFun (tateBase K p) (isUnit_Δ_tateBase K p) _ hc = 0) :
    G.toFun (E₁ K p) (isUnit_Δ_E₁ K p) (D₁ (p := p) ζ) (isLevelPStructure_D₁ ζ hc) = 0 := by
  have h1 : G.toFun (tateΩ K p) (isUnit_Δ_tateΩ K p) (D₀Ω ζ) (isLevelPStructure_D₀Ω ζ hc) = 0 := by
    have h := map_toFun' G (ι₀ₐ K p) (tateBase K p) (isUnit_Δ_tateBase K p) _ hc
    rw [h0, map_zero] at h
    rw [← h.symm]
    exact toFun_congr G _ _ _ _ (by rw [coe_ι₀ₐ]; rfl) (by rw [coe_ι₀ₐ]; rfl)
  have h2 := G.toFun_variableChange (Cgen K p) (tateΩ K p) (isUnit_Δ_tateΩ K p) (isUnit_Δ_E₁ K p)
    (D₀Ω ζ) (isLevelPStructure_D₀Ω ζ hc) (isLevelPStructure_D₁ ζ hc)
  rw [h1, mul_zero] at h2
  exact h2

variable (K p)

abbrev Ωbar : Type u := AlgebraicClosure (Ω K p)

def e₁ : Generic.FunctionField K →ₐ[K] Ω K p :=
  IsFractionRing.liftAlgHom (K := Generic.FunctionField K) (g := Generic.classify K (E₁ K p))
    (classify_E₁_injective K p)

theorem e₁_algebraMap (x : MvPolynomial (Fin 5) K) :
    e₁ K p (algebraMap (MvPolynomial (Fin 5) K) (Generic.FunctionField K) x) =
      Generic.classify K (E₁ K p) x := by
  rw [e₁, IsFractionRing.liftAlgHom_apply]
  exact IsFractionRing.lift_algebraMap _ x

@[reducible] def algFΩbar : Algebra (Generic.FunctionField K) (Ωbar K p) :=
  ((algebraMap (Ω K p) (Ωbar K p)).comp (e₁ K p : Generic.FunctionField K →+* Ω K p)).toAlgebra

def ιbar : Generic.Closure K →+* Ωbar K p :=
  letI := algFΩbar K p
  ((IsAlgClosed.lift (R := Generic.FunctionField K) (S := Generic.Closure K) (M := Ωbar K p) :
      Generic.Closure K →ₐ[Generic.FunctionField K] Ωbar K p) : Generic.Closure K →+* Ωbar K p)

theorem ιbar_comp_algebraMap :
    (ιbar K p).comp (algebraMap (Generic.FunctionField K) (Generic.Closure K)) =
      (algebraMap (Ω K p) (Ωbar K p)).comp (e₁ K p : Generic.FunctionField K →+* Ω K p) := by
  letI := algFΩbar K p
  refine RingHom.ext fun x => ?_
  exact (IsAlgClosed.lift (R := Generic.FunctionField K) (S := Generic.Closure K)
    (M := Ωbar K p)).commutes x

theorem ιbar_algebraMap (x : Generic.FunctionField K) :
    ιbar K p (algebraMap (Generic.FunctionField K) (Generic.Closure K) x) =
      algebraMap (Ω K p) (Ωbar K p) (e₁ K p x) :=
  congrArg (fun φ : Generic.FunctionField K →+* Ωbar K p => φ x) (ιbar_comp_algebraMap K p)

def ιbarₐ : Generic.Closure K →ₐ[K] Ωbar K p :=
  { ιbar K p with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply K (Generic.FunctionField K) (Generic.Closure K),
        ιbar_algebraMap, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }

@[scoped simp] theorem coe_ιbarₐ : ((ιbarₐ K p : Generic.Closure K →ₐ[K] Ωbar K p) :
    Generic.Closure K →+* Ωbar K p) = ιbar K p :=
  RingHom.ext fun _ => rfl

theorem curve_map_ιbar :
    (Generic.curve K).map (ιbar K p) = (E₁ K p).map (algebraMap (Ω K p) (Ωbar K p)) := by
  rw [Generic.curve_def, WeierstrassCurve.map_map,
    IsScalarTower.algebraMap_eq (MvPolynomial (Fin 5) K) (Generic.FunctionField K) (Generic.Closure K),
    ← RingHom.comp_assoc, ιbar_comp_algebraMap, RingHom.comp_assoc]
  have hcl : (e₁ K p : Generic.FunctionField K →+* Ω K p).comp
      (algebraMap (MvPolynomial (Fin 5) K) (Generic.FunctionField K)) =
      (Generic.classify K (E₁ K p) : MvPolynomial (Fin 5) K →+* Ω K p) := by
    ext x
    · exact e₁_algebraMap K p _
    · exact e₁_algebraMap K p _
  rw [hcl, ← WeierstrassCurve.map_map, Generic.poly_map_classify]

omit [NeZero p] in
theorem natCast_closure_ne_zero (hp : (p : K) ≠ 0) : (p : Generic.Closure K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (Generic.Closure K)) p]
  exact (map_ne_zero_iff _ (algebraMap K (Generic.Closure K)).injective).mpr hp

variable {K p}

include hc in

theorem exists_toFun_genericCurve_eq_zero (hp : (p : K) ≠ 0)
    (h0 : G.toFun (tateBase K p) (isUnit_Δ_tateBase K p) _ hc = 0) :
    ∃ (D₀ : LevelPData (Generic.Closure K)) (hD₀ : IsLevelPStructure (Generic.curve K) p D₀),
      G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D₀ hD₀ = 0 := by

  let f : Ω K p →ₐ[K] Ωbar K p := IsScalarTower.toAlgHom K (Ω K p) (Ωbar K p)
  have hf : (f : Ω K p →+* Ωbar K p) = algebraMap (Ω K p) (Ωbar K p) := rfl
  let D₂ : LevelPData (Ωbar K p) := (D₁ (p := p) ζ).map (algebraMap (Ω K p) (Ωbar K p))
  have hD₂ : IsLevelPStructure ((E₁ K p).map (algebraMap (Ω K p) (Ωbar K p))) p D₂ :=
    (isLevelPStructure_D₁ ζ hc).map _
  have hval₂ : G.toFun ((E₁ K p).map (algebraMap (Ω K p) (Ωbar K p)))
      (KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_E₁ K p)) D₂ hD₂ = 0 := by
    have h := map_toFun' G f (E₁ K p) (isUnit_Δ_E₁ K p) _ (isLevelPStructure_D₁ ζ hc)
    rw [toFun_E₁_eq_zero G ζ hc h0, map_zero] at h
    rw [← h.symm]
    exact toFun_congr G _ _ _ _ (by rw [hf]) (by rw [hf])

  letI : Algebra (Generic.Closure K) (Ωbar K p) := (ιbar K p).toAlgebra
  have halg : algebraMap (Generic.Closure K) (Ωbar K p) = ιbar K p := rfl
  have hD₂' : IsLevelPStructure ((Generic.curve K).map (algebraMap (Generic.Closure K) (Ωbar K p)))
      p D₂ := by
    rw [halg, curve_map_ιbar]; exact hD₂
  obtain ⟨D₀, hD₀, hmap⟩ :=
    exists_levelPData_map_eq (natCast_closure_ne_zero K p hp) (Generic.curve K) D₂ hD₂'
  refine ⟨D₀, hD₀, ?_⟩

  have h := map_toFun' G (ιbarₐ K p) (Generic.curve K) (Generic.isUnit_Δ_curve K) D₀ hD₀
  have e : G.toFun ((Generic.curve K).map (ιbarₐ K p : Generic.Closure K →+* Ωbar K p))
      (KatzModularForm.isUnit_Δ_map _ (Generic.isUnit_Δ_curve K))
      (D₀.map (ιbarₐ K p : Generic.Closure K →+* Ωbar K p)) (hD₀.map _) =
      G.toFun ((E₁ K p).map (algebraMap (Ω K p) (Ωbar K p)))
      (KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_E₁ K p)) D₂ hD₂ :=
    toFun_congr G _ _ _ _ (by rw [coe_ιbarₐ, curve_map_ιbar]) (by rw [coe_ιbarₐ, ← halg, hmap])
  rw [e, hval₂] at h
  have hinj : Function.Injective (ιbarₐ K p) :=
    (ιbarₐ K p : Generic.Closure K →+* Ωbar K p).injective
  exact (map_eq_zero_iff _ hinj).mp h

end Dominance

end ModularCurve.QExpFieldProof
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve.QExpFieldProof"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "tateLaurent qExpand qExpand_C qExpand_injective indepElt indepElt_map LevelPData LevelPData.map LevelPData.map_xP LevelPData.map_xQ LevelPData.variableChange_xP LevelPData.variableChange_xQ IsLevelPStructure KatzLevelPForm cuspData algebraMap_laurentSeries_apply isUnit_Δ_tateBase tateBase KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero algebraicIndependent_variableChange_tateLaurent" namespace QExpFieldProof end ModularCurve.QExpFieldProof
p2m_open_scoped "ModularCurve" in
p2m_open "WeierstrassCurve~cusp" in open _root_.ModularCurve _root_.P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve ModularCurve.QExpFieldProof  in

theorem ModularCurve.QExpFieldProof.toFun_genericCurve_eq_zero_of_exists
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) {k : ℤ}
    (G : KatzLevelPForm K p k) (hG : G.DependsOnlyOnSndLine)
    {D₀ : LevelPData (Generic.Closure K)} (hD₀ : IsLevelPStructure (Generic.curve K) p D₀)
    (h0 : G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D₀ hD₀ = 0)
    (D : LevelPData (Generic.Closure K)) (hD : IsLevelPStructure (Generic.curve K) p D) :
    G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D hD = 0 := by
  obtain ⟨σ, hσ⟩ := Generic.exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero hp2 hp
    hD₀.preΨ_Q hD.preΨ_Q
  have hσD := isLevelPStructure_map_algEquiv σ hD₀
  have h1 : G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K)
      (D₀.map (σ : Generic.Closure K →+* Generic.Closure K)) hσD = 0 := by
    rw [toFun_map_algEquiv G σ D₀ hD₀ hσD, h0, map_zero]
  have h2 := hG (Generic.curve K) (Generic.isUnit_Δ_curve K)
    (D₀.map (σ : Generic.Closure K →+* Generic.Closure K)) D hσD hD (by simpa using hσ)
  rw [h2, h1]

end
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve.QExpFieldProof"

p2m_open "WeierstrassCurve~cusp" in open _root_.ModularCurve _root_.P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.ModularCurve ModularCurve.QExpFieldProof  in
theorem solution
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (ζ : Kˣ) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase K p) p
      (ModularCurve.cuspData K p ζ ![1, 0] ![0, 1]))
    (G : ModularCurve.KatzLevelPForm K p k) (hG : G.DependsOnlyOnSndLine)
    (h0 : G.toFun (ModularCurve.tateBase K p) (ModularCurve.isUnit_Δ_tateBase K p) _ hc = 0) :
    G = 0 := by

  obtain ⟨D₀, hD₀, hG₀⟩ := exists_toFun_genericCurve_eq_zero G ζ hc hp h0

  exact KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero hp2 hp G
    fun D hD => toFun_genericCurve_eq_zero_of_exists hp2 hp G hG hD₀ hG₀ D hD

end S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
end P2MW
export P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field (solution)
