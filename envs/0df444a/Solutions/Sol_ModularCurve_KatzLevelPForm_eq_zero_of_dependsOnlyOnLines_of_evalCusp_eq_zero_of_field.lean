-- Prove2me | solution 1 for ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/99e7e1b4-5d4a-5a6a-9792-a9746f4c8ad8

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_WeierstrassCurve_Generic
import Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero
import Theorems.Thm_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
import Theorems.Thm_ModularCurve_algebraicIndependent_variableChange_tateLaurent
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Theorems.Thm_ModularCurve_cuspData_map_qTwist
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

noncomputable section

p2m_open "Polynomial WeierstrassCurve~cusp"

namespace ModularCurve
p2m_export "ModularCurve" "tateLaurent qExpand qExpand_C qExpand_injective indepElt InLine indepElt_map LevelPData LevelPData.map LevelPData.map_xP LevelPData.map_yP LevelPData.map_xQ LevelPData.map_yQ LevelPData.map_map LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ IsLevelPStructure KatzLevelPForm LevelPData.yQ LevelPData.xP LevelPData.yP LevelPData.ext LevelPData.xQ cuspData cuspShift algebraMap_laurentSeries_apply tateBase_map_qTwist isUnit_Δ_tateBase tateBase qTwist qTwist_single qTwist_one_apply qTwist_qTwist KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero algebraicIndependent_variableChange_tateLaurent cuspData_map_qTwist indepElt_eq_zero_iff_mem_zmultiples"
namespace QExpSplitField
p2m_open "ModularCurve"

section TwoTransitive

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] {p : ℕ} [hp : Fact p.Prime]

theorem pow_smul_line (σ : Γ) (ℓ : ZMod p → X) (hσ : ∀ a, σ • ℓ a = ℓ (a + 1)) (n : ℕ)
    (a : ZMod p) : σ ^ n • ℓ a = ℓ (a + n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, hσ, ih]
    congr 1
    push_cast
    ring

theorem line_injective (σ : Γ) (ℓ : ZMod p → X) (hσ : ∀ a, σ • ℓ a = ℓ (a + 1))
    (h01 : ℓ 0 ≠ ℓ 1) : Function.Injective ℓ := by
  intro a b hab
  by_contra hne

  have hper : ∀ c : ZMod p, ℓ (c + (b - a)) = ℓ c := by
    intro c
    have h := pow_smul_line σ ℓ hσ (c - a).val a
    rw [hab, pow_smul_line σ ℓ hσ, ZMod.natCast_zmod_val] at h
    have e1 : a + (c - a) = c := by ring
    have e2 : b + (c - a) = c + (b - a) := by ring
    rw [e1, e2] at h
    exact h
  have hmul : ∀ n : ℕ, ℓ ((n : ZMod p) * (b - a)) = ℓ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hper, ih]
  have hd : (b - a : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h1 : (((b - a)⁻¹).val : ZMod p) * (b - a) = 1 := by
    rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hd]
  have h := hmul ((b - a)⁻¹).val
  rw [h1] at h
  exact h01 h.symm

variable [Finite X]

theorem exists_compl_range_eq_singleton (hcard : Nat.card X = p + 1) (ℓ : ZMod p → X)
    (hℓ : Function.Injective ℓ) : ∃ t : X, ∀ x, x ∉ Set.range ℓ ↔ x = t := by
  classical
  haveI := Fintype.ofFinite X
  have hc : (Finset.univ.filter fun x => x ∉ Set.range ℓ).card = 1 := by
    have h1 : (Finset.univ.filter fun x => x ∈ Set.range ℓ).card = p := by
      have e : (Finset.univ.filter fun x => x ∈ Set.range ℓ) = Finset.univ.image ℓ := by
        ext x
        simp
      rw [e, Finset.card_image_of_injective _ hℓ, Finset.card_univ, ZMod.card]
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (fun x => x ∈ Set.range ℓ)
    rw [h1, Finset.card_univ, Fintype.card_eq_nat_card, hcard] at h2
    omega
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc
  refine ⟨t, fun x => ?_⟩
  have h := Finset.ext_iff.mp ht x
  simpa using h

theorem two_transitive (hcard : Nat.card X = p + 1) (htrans : ∀ x y : X, ∃ g : Γ, g • x = y)
    (σ : Γ) (ℓ : ZMod p → X) (hσ : ∀ a, σ • ℓ a = ℓ (a + 1)) (h01 : ℓ 0 ≠ ℓ 1)
    {x₁ x₂ y₁ y₂ : X} (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) : ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂ := by
  have hℓ := line_injective σ ℓ hσ h01
  obtain ⟨t, ht⟩ := exists_compl_range_eq_singleton hcard ℓ hℓ

  have hσt : σ • t = t := by
    refine (ht (σ • t)).mp ?_
    rintro ⟨a, ha⟩
    have h := hσ (a - 1)
    rw [sub_add_cancel] at h
    exact ((ht t).mpr rfl) ⟨a - 1, smul_left_cancel σ (h.trans ha)⟩
  have hσnt : ∀ n : ℕ, σ ^ n • t = t := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hσt, ih]

  have key : ∀ {u v : X}, u ≠ v → ∃ (g : Γ) (a : ZMod p), g • u = t ∧ g • v = ℓ a := by
    intro u v huv
    obtain ⟨g, hg⟩ := htrans u t
    have hgv : g • v ∈ Set.range ℓ := by
      by_contra h
      rw [ht] at h
      exact huv (smul_left_cancel g (hg.trans h.symm))
    obtain ⟨a, ha⟩ := hgv
    exact ⟨g, a, hg, ha.symm⟩
  obtain ⟨g₁, a, hg₁, hg₁'⟩ := key hx
  obtain ⟨g₂, b, hg₂, hg₂'⟩ := key hy
  refine ⟨g₂⁻¹ * σ ^ (b - a).val * g₁, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hg₁, hσnt, ← hg₂, inv_smul_smul]
  · rw [mul_smul, mul_smul, hg₁', pow_smul_line σ ℓ hσ, ZMod.natCast_zmod_val, add_sub_cancel,
      ← hg₂', inv_smul_smul]

end TwoTransitive

p2m_open "ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve"

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

end Dominance

section Cusp

variable {K : Type u} [Field K] {p : ℕ} [NeZero p] {k : ℤ}

def D₁ (c : LevelPData (LaurentSeries K)) : LevelPData (Ω K p) :=
  (c.map (ι₀ K p)).variableChange (Cgen K p)

theorem isLevelPStructure_D₁ {c : LevelPData (LaurentSeries K)}
    (hc : IsLevelPStructure (tateBase K p) p c) : IsLevelPStructure (E₁ K p) p (D₁ c) :=
  (show IsLevelPStructure (tateΩ K p) p (c.map (ι₀ K p)) from hc.map _).variableChange (Cgen K p)

theorem toFun_E₁_eq_zero (G : KatzLevelPForm K p k) {c : LevelPData (LaurentSeries K)}
    (hc : IsLevelPStructure (tateBase K p) p c)
    (h0 : G.toFun (tateBase K p) (isUnit_Δ_tateBase K p) c hc = 0) :
    G.toFun (E₁ K p) (isUnit_Δ_E₁ K p) (D₁ c) (isLevelPStructure_D₁ hc) = 0 := by
  have hc' : IsLevelPStructure (tateΩ K p) p (c.map (ι₀ K p)) := hc.map _
  have h1 : G.toFun (tateΩ K p) (isUnit_Δ_tateΩ K p) (c.map (ι₀ K p)) hc' = 0 := by
    have h := map_toFun' G (ι₀ₐ K p) (tateBase K p) (isUnit_Δ_tateBase K p) _ hc
    rw [h0, map_zero] at h
    rw [← h.symm]
    exact toFun_congr G _ _ _ _ (by rw [coe_ι₀ₐ]; rfl) (by rw [coe_ι₀ₐ])
  have h2 := G.toFun_variableChange (Cgen K p) (tateΩ K p) (isUnit_Δ_tateΩ K p) (isUnit_Δ_E₁ K p)
    (c.map (ι₀ K p)) hc' (isLevelPStructure_D₁ hc)
  rw [h1, mul_zero] at h2
  exact h2

def D₂ (c : LevelPData (LaurentSeries K)) : LevelPData (Ωbar K p) :=
  (D₁ c).map (algebraMap (Ω K p) (Ωbar K p))

theorem isLevelPStructure_D₂ {c : LevelPData (LaurentSeries K)}
    (hc : IsLevelPStructure (tateBase K p) p c) :
    IsLevelPStructure ((Generic.curve K).map (ιbar K p)) p (D₂ c) := by
  rw [curve_map_ιbar]
  exact (isLevelPStructure_D₁ hc).map _

open Classical in

def desc (z : Ωbar K p) : Generic.Closure K :=
  if h : ∃ x, ιbar K p x = z then h.choose else 0

theorem ιbar_desc {z : Ωbar K p} (h : ∃ x, ιbar K p x = z) : ιbar K p (desc z) = z := by
  classical
  rw [desc, dif_pos h]
  exact h.choose_spec

theorem desc_ιbar (x : Generic.Closure K) : desc (ιbar K p x) = x :=
  (ιbar K p).injective (ιbar_desc ⟨x, rfl⟩)

def descD (D : LevelPData (Ωbar K p)) : LevelPData (Generic.Closure K) :=
  ⟨desc D.xP, desc D.yP, desc D.xQ, desc D.yQ⟩

theorem descD_map (D : LevelPData (Generic.Closure K)) : descD (D.map (ιbar K p)) = D := by
  rcases D with ⟨a, b, c, d⟩
  simp only [descD, LevelPData.map, desc_ιbar]

theorem descD_spec (hp : (p : K) ≠ 0) {D : LevelPData (Ωbar K p)}
    (hD : IsLevelPStructure ((Generic.curve K).map (ιbar K p)) p D) :
    (descD D).map (ιbar K p) = D ∧ IsLevelPStructure (Generic.curve K) p (descD D) := by
  letI : Algebra (Generic.Closure K) (Ωbar K p) := (ιbar K p).toAlgebra
  have halg : algebraMap (Generic.Closure K) (Ωbar K p) = ιbar K p := rfl
  obtain ⟨D₀, hD₀, hmap⟩ := exists_levelPData_map_eq (natCast_closure_ne_zero K p hp)
    (Generic.curve K) D (by rw [halg]; exact hD)
  rw [halg] at hmap
  rw [← hmap, descD_map]
  exact ⟨rfl, hD₀⟩

variable (p) in

def D₃ (c : LevelPData (LaurentSeries K)) : LevelPData (Generic.Closure K) := descD (D₂ (p := p) c)

theorem D₃_map (hp : (p : K) ≠ 0) {c : LevelPData (LaurentSeries K)}
    (hc : IsLevelPStructure (tateBase K p) p c) : (D₃ p c).map (ιbar K p) = D₂ c :=
  (descD_spec hp (isLevelPStructure_D₂ hc)).1

theorem isLevelPStructure_D₃ (hp : (p : K) ≠ 0) {c : LevelPData (LaurentSeries K)}
    (hc : IsLevelPStructure (tateBase K p) p c) : IsLevelPStructure (Generic.curve K) p (D₃ p c) :=
  (descD_spec hp (isLevelPStructure_D₂ hc)).2

theorem toFun_D₃_eq_zero (hp : (p : K) ≠ 0) (G : KatzLevelPForm K p k)
    {c : LevelPData (LaurentSeries K)} (hc : IsLevelPStructure (tateBase K p) p c)
    (h0 : G.toFun (tateBase K p) (isUnit_Δ_tateBase K p) c hc = 0) :
    G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) (D₃ p c) (isLevelPStructure_D₃ hp hc) = 0 := by
  let f : Ω K p →ₐ[K] Ωbar K p := IsScalarTower.toAlgHom K (Ω K p) (Ωbar K p)
  have hf : (f : Ω K p →+* Ωbar K p) = algebraMap (Ω K p) (Ωbar K p) := rfl
  have hD₂ : IsLevelPStructure ((E₁ K p).map (algebraMap (Ω K p) (Ωbar K p))) p (D₂ c) :=
    (isLevelPStructure_D₁ hc).map _
  have hval₂ : G.toFun ((E₁ K p).map (algebraMap (Ω K p) (Ωbar K p)))
      (KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_E₁ K p)) (D₂ c) hD₂ = 0 := by
    have h := map_toFun' G f (E₁ K p) (isUnit_Δ_E₁ K p) _ (isLevelPStructure_D₁ hc)
    rw [toFun_E₁_eq_zero G hc h0, map_zero] at h
    rw [← h.symm]
    exact toFun_congr G _ _ _ _ (by rw [hf]) (by rw [hf]; rfl)
  have h := map_toFun' G (ιbarₐ K p) (Generic.curve K) (Generic.isUnit_Δ_curve K) (D₃ p c)
    (isLevelPStructure_D₃ hp hc)
  have e : G.toFun ((Generic.curve K).map (ιbarₐ K p : Generic.Closure K →+* Ωbar K p))
      (KatzModularForm.isUnit_Δ_map _ (Generic.isUnit_Δ_curve K))
      ((D₃ p c).map (ιbarₐ K p : Generic.Closure K →+* Ωbar K p)) ((isLevelPStructure_D₃ hp hc).map _) =
      G.toFun ((E₁ K p).map (algebraMap (Ω K p) (Ωbar K p)))
      (KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_E₁ K p)) (D₂ c) hD₂ :=
    toFun_congr G _ _ _ _ (by rw [coe_ιbarₐ, curve_map_ιbar]) (by rw [coe_ιbarₐ, D₃_map hp hc])
  rw [e, hval₂] at h
  have hinj : Function.Injective (ιbarₐ K p) :=
    (ιbarₐ K p : Generic.Closure K →+* Ωbar K p).injective
  exact (map_eq_zero_iff _ hinj).mp h

end Cusp

section Twist

variable (K : Type u) [Field K] (p : ℕ) (ζ : Kˣ)

def τL : LaurentSeries K ≃+* LaurentSeries K :=
  { qTwist ζ with
    invFun := qTwist ζ⁻¹
    left_inv := fun f => by
      show qTwist ζ⁻¹ (qTwist ζ f) = f
      rw [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply]
    right_inv := fun f => by
      show qTwist ζ (qTwist ζ⁻¹ f) = f
      rw [qTwist_qTwist, mul_inv_cancel, qTwist_one_apply] }

@[scoped simp] theorem τL_apply (f : LaurentSeries K) : τL K ζ f = qTwist ζ f := rfl

def τP : MvPolynomial (Fin 4) (LaurentSeries K) ≃+* MvPolynomial (Fin 4) (LaurentSeries K) :=
  MvPolynomial.mapEquiv (Fin 4) (τL K ζ)

theorem τP_apply (x : MvPolynomial (Fin 4) (LaurentSeries K)) :
    τP K ζ x = MvPolynomial.map (qTwist ζ) x := by
  rw [τP, MvPolynomial.mapEquiv_apply]
  rfl

def τΩ : Ω K p ≃+* Ω K p :=
  (IsFractionRing.ringEquivOfRingEquiv (τP K ζ) : Ω K p ≃+* Ω K p)

theorem τΩ_ιP (x : MvPolynomial (Fin 4) (LaurentSeries K)) :
    τΩ K p ζ (ιP K p x) = ιP K p (τP K ζ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (τP K ζ) x

theorem τΩ_ι₀ (f : LaurentSeries K) : τΩ K p ζ (ι₀ K p f) = ι₀ K p (qTwist ζ f) := by
  show τΩ K p ζ (ιP K p (MvPolynomial.C f)) = ιP K p (MvPolynomial.C (qTwist ζ f))
  rw [τΩ_ιP, τP_apply, MvPolynomial.map_C]

theorem τΩ_gen (i : Fin 4) : τΩ K p ζ (gen K p i) = gen K p i := by
  show τΩ K p ζ (ιP K p (MvPolynomial.X i)) = ιP K p (MvPolynomial.X i)
  rw [τΩ_ιP, τP_apply, MvPolynomial.map_X]

theorem τΩ_jK (r : K) : τΩ K p ζ (jK K p r) = jK K p r := by
  show τΩ K p ζ (ι₀ K p (HahnSeries.C r)) = ι₀ K p (HahnSeries.C r)
  rw [τΩ_ι₀, HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]

theorem Cgen_map_τΩ : (Cgen K p).map (τΩ K p ζ : Ω K p →+* Ω K p) = Cgen K p := by
  simp only [Cgen, VariableChange.map]
  congr 1
  · exact Units.ext (τΩ_gen K p ζ 0)
  · exact τΩ_gen K p ζ 1
  · exact τΩ_gen K p ζ 2
  · exact τΩ_gen K p ζ 3

def τbar : Ωbar K p ≃+* Ωbar K p :=
  IsAlgClosure.equivOfEquiv (Ωbar K p) (Ωbar K p) (τΩ K p ζ)

theorem τbar_algebraMap (x : Ω K p) :
    τbar K p ζ (algebraMap (Ω K p) (Ωbar K p) x) = algebraMap (Ω K p) (Ωbar K p) (τΩ K p ζ x) :=
  IsAlgClosure.equivOfEquiv_algebraMap (Ωbar K p) (Ωbar K p) (τΩ K p ζ) x

variable [NeZero p] (hζ : ζ ^ p = 1)
include hζ

theorem tateΩ_map_τΩ : (tateΩ K p).map (τΩ K p ζ : Ω K p →+* Ω K p) = tateΩ K p := by
  rw [tateΩ, WeierstrassCurve.map_map]
  have hc : (τΩ K p ζ : Ω K p →+* Ω K p).comp (ι₀ K p) = (ι₀ K p).comp (qTwist ζ) :=
    RingHom.ext fun f => τΩ_ι₀ K p ζ f
  rw [hc, ← WeierstrassCurve.map_map, tateBase_map_qTwist p ζ hζ]

theorem E₁_map_τΩ : (E₁ K p).map (τΩ K p ζ : Ω K p →+* Ω K p) = E₁ K p := by
  rw [E₁, ← WeierstrassCurve.map_variableChange, Cgen_map_τΩ, tateΩ_map_τΩ K p ζ hζ]

theorem τΩ_e₁ (x : Generic.FunctionField K) : τΩ K p ζ (e₁ K p x) = e₁ K p x := by
  have hcl : (τΩ K p ζ : Ω K p →+* Ω K p).comp
      (Generic.classify K (E₁ K p) : MvPolynomial (Fin 5) K →+* Ω K p) =
      (Generic.classify K (E₁ K p) : MvPolynomial (Fin 5) K →+* Ω K p) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, AlgHom.coe_toRingHom, MvPolynomial.algHom_C, algebraMap_K_eq]
      exact τΩ_jK K p ζ r
    · rw [RingHom.comp_apply, AlgHom.coe_toRingHom, Generic.classify_X]
      have h := E₁_map_τΩ K p ζ hζ
      fin_cases i
      · exact congrArg WeierstrassCurve.a₁ h
      · exact congrArg WeierstrassCurve.a₂ h
      · exact congrArg WeierstrassCurve.a₃ h
      · exact congrArg WeierstrassCurve.a₄ h
      · exact congrArg WeierstrassCurve.a₆ h
  have key : (τΩ K p ζ : Ω K p →+* Ω K p).comp (e₁ K p : Generic.FunctionField K →+* Ω K p) =
      (e₁ K p : Generic.FunctionField K →+* Ω K p) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin 5) K)) ?_
    refine RingHom.ext fun y => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, AlgHom.coe_toRingHom,
      e₁_algebraMap]
    have h := RingHom.congr_fun hcl y
    rwa [RingHom.comp_apply, AlgHom.coe_toRingHom] at h
  exact congrArg (fun φ : Generic.FunctionField K →+* Ω K p => φ x) key

end Twist

namespace LevelPData
private theorem _root_.ModularCurve.QExpSplitField.LevelPData.map_variableChange {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).map φ = (D.map φ).variableChange (C.map φ) := by
  have hu : φ ((C.u⁻¹ : Aˣ) : A) = (((C.map φ).u⁻¹ : Bˣ) : B) := (Units.coe_map_inv (φ : A →* B) C.u).symm
  refine LevelPData.ext ?_ ?_ ?_ ?_ <;>
    simp only [LevelPData.map_xP, LevelPData.map_yP, LevelPData.map_xQ, LevelPData.map_yQ,
      LevelPData.variableChange_xP, LevelPData.variableChange_yP, LevelPData.variableChange_xQ,
      LevelPData.variableChange_yQ, map_mul, map_sub, map_pow, hu, VariableChange.map]

end LevelPData
p2m_export "ModularCurve.QExpSplitField" "LevelPData.map_variableChange"
namespace LevelPData
private theorem _root_.ModularCurve.QExpSplitField.LevelPData.map_injective {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : Function.Injective φ) {D D' : LevelPData A} (h : D.map φ = D'.map φ) : D = D' := by
  have h1 := congrArg LevelPData.xP h
  have h2 := congrArg LevelPData.yP h
  have h3 := congrArg LevelPData.xQ h
  have h4 := congrArg LevelPData.yQ h
  simp only [LevelPData.map_xP, LevelPData.map_yP, LevelPData.map_xQ, LevelPData.map_yQ] at h1 h2 h3 h4
  exact LevelPData.ext (hφ h1) (hφ h2) (hφ h3) (hφ h4)

end LevelPData
p2m_export "ModularCurve.QExpSplitField" "LevelPData.map_injective"
section Sigma

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : ζ ^ p = 1)

@[reducible] def algCΩbar : Algebra (Generic.Closure K) (Ωbar K p) := (ιbar K p).toAlgebra

attribute [local instance] algFΩbar algCΩbar

theorem towerFCΩbar : IsScalarTower (Generic.FunctionField K) (Generic.Closure K) (Ωbar K p) :=
  IsScalarTower.of_algebraMap_eq fun x => (ιbar_algebraMap K p x).symm

attribute [local instance] towerFCΩbar

def τbarₐ : Ωbar K p ≃ₐ[Generic.FunctionField K] Ωbar K p :=
  AlgEquiv.ofRingEquiv (f := τbar K p ζ) fun x => by
    show τbar K p ζ (algebraMap (Ω K p) (Ωbar K p) (e₁ K p x)) =
      algebraMap (Ω K p) (Ωbar K p) (e₁ K p x)
    rw [τbar_algebraMap, τΩ_e₁ K p ζ hζ]

def σK : Generic.Closure K ≃ₐ[Generic.FunctionField K] Generic.Closure K :=
  (τbarₐ K p ζ hζ).restrictNormal (Generic.Closure K)

theorem ιbar_σK (x : Generic.Closure K) : ιbar K p (σK K p ζ hζ x) = τbar K p ζ (ιbar K p x) :=
  AlgEquiv.restrictNormal_commutes (τbarₐ K p ζ hζ) (Generic.Closure K) x

include hζ in
theorem D₁_map_τΩ (v w : Fin 2 → ZMod p) :
    (D₁ (cuspData K p ζ v w)).map (τΩ K p ζ : Ω K p →+* Ω K p) =
      D₁ (p := p) (cuspData K p ζ (cuspShift p v) (cuspShift p w)) := by
  rw [D₁, D₁, LevelPData.map_variableChange, Cgen_map_τΩ, LevelPData.map_map]
  have hc : (τΩ K p ζ : Ω K p →+* Ω K p).comp (ι₀ K p) = (ι₀ K p).comp (qTwist ζ) :=
    RingHom.ext fun f => τΩ_ι₀ K p ζ f
  rw [hc, ← LevelPData.map_map,
    ModularCurve.cuspData_map_qTwist (R := K) (p := p) (ζ := ζ) (hζ := hζ) (v := v) (w := w)]

include hζ in
theorem D₂_map_τbar (v w : Fin 2 → ZMod p) :
    (D₂ (cuspData K p ζ v w)).map (τbar K p ζ : Ωbar K p →+* Ωbar K p) =
      D₂ (p := p) (cuspData K p ζ (cuspShift p v) (cuspShift p w)) := by
  rw [D₂, D₂, LevelPData.map_map]
  have hc : (τbar K p ζ : Ωbar K p →+* Ωbar K p).comp (algebraMap (Ω K p) (Ωbar K p)) =
      (algebraMap (Ω K p) (Ωbar K p)).comp (τΩ K p ζ : Ω K p →+* Ω K p) :=
    RingHom.ext fun x => τbar_algebraMap K p ζ x
  rw [hc, ← LevelPData.map_map, D₁_map_τΩ K p ζ hζ]

theorem D₃_map_σK (hp : (p : K) ≠ 0) {v w : Fin 2 → ZMod p}
    (hc : IsLevelPStructure (tateBase K p) p (cuspData K p ζ v w))
    (hc' : IsLevelPStructure (tateBase K p) p (cuspData K p ζ (cuspShift p v) (cuspShift p w))) :
    (D₃ p (cuspData K p ζ v w)).map (σK K p ζ hζ : Generic.Closure K →+* Generic.Closure K) =
      D₃ p (cuspData K p ζ (cuspShift p v) (cuspShift p w)) := by
  refine LevelPData.map_injective (ιbar K p).injective ?_
  have hcomp : (ιbar K p).comp (σK K p ζ hζ : Generic.Closure K →+* Generic.Closure K) =
      (τbar K p ζ : Ωbar K p →+* Ωbar K p).comp (ιbar K p) :=
    RingHom.ext fun x => ιbar_σK K p ζ hζ x
  rw [LevelPData.map_map, hcomp, ← LevelPData.map_map, D₃_map hp hc, D₂_map_τbar K p ζ hζ,
    D₃_map hp hc']

end Sigma

section Torsion

open scoped LinearAlgebra.Projectivization
open WeierstrassCurve.Affine

variable (K : Type u) [Field K] (p : ℕ)

@[reducible] def decEqC : DecidableEq (Generic.Closure K) := Classical.decEq _

attribute [local instance] decEqC

abbrev EL : WeierstrassCurve (Generic.FunctionField K) :=
  (Generic.poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Generic.FunctionField K))

abbrev Egen : WeierstrassCurve (Generic.Closure K) := (EL K).baseChange (Generic.Closure K)

theorem curve_eq_Egen : Generic.curve K = Egen K := by
  rw [Generic.curve_def]
  show _ = ((Generic.poly K).map _).map _
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

theorem Δ_EL_ne_zero : (EL K).Δ ≠ 0 := by
  rw [WeierstrassCurve.map_Δ]
  exact (map_ne_zero_iff _ (Generic.algebraMap_functionField_injective K)).2 (Generic.Δ_poly_ne_zero K)

scoped instance isElliptic_EL : (EL K).IsElliptic := ⟨(Δ_EL_ne_zero K).isUnit⟩

scoped instance isElliptic_Egen : (Egen K).IsElliptic := by
  rw [← curve_eq_Egen]
  infer_instance

abbrev Pt : Type u := (Egen K).toAffine.Point

abbrev Tor : Submodule ℤ (Pt K) := Submodule.torsionBy ℤ (Pt K) (p : ℕ)

theorem p_smul_tor (x : Tor K p) : p • x = 0 := by
  apply Subtype.ext
  have h := x.2
  rw [Submodule.mem_torsionBy_iff] at h
  rw [Submodule.coe_smul_of_tower, Submodule.coe_zero, ← natCast_zsmul]
  exact h

@[reducible] def modTor : Module (ZMod p) (Tor K p) := AddCommGroup.zmodModule (p_smul_tor K p)

attribute [local instance] modTor

theorem natCast_closure_ne_zero' (hp : (p : K) ≠ 0) : (p : Generic.Closure K) ≠ 0 :=
  natCast_closure_ne_zero K p hp

variable [hprime : Fact p.Prime]

theorem finrank_tor (hp : (p : K) ≠ 0) : Module.finrank (ZMod p) (Tor K p) = 2 := by
  have hpC := natCast_closure_ne_zero' K p hp
  have hcard : Nat.card (Tor K p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (EL K) (K := Generic.Closure K) hpC
  haveI : Finite (Tor K p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hprime.out.ne_zero)
  haveI : Module.Finite (ZMod p) (Tor K p) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Tor K p)
  rw [hcard, Nat.card_zmod] at h
  exact (Nat.pow_right_injective hprime.out.two_le h).symm

theorem card_lines (hp : (p : K) ≠ 0) : Nat.card (ℙ (ZMod p) (Tor K p)) = p + 1 := by
  rw [Projectivization.card_of_finrank_two (ZMod p) (Tor K p) (finrank_tor K p hp), Nat.card_zmod]

variable {K p}

def pt (x y : Generic.Closure K) (h : (Egen K).toAffine.Equation x y) : Pt K :=
  Point.some x y ((equation_iff_nonsingular ..).mp h)

theorem pt_ne_zero (x y : Generic.Closure K) (h : (Egen K).toAffine.Equation x y) : pt x y h ≠ 0 :=
  Point.some_ne_zero _

theorem p_nsmul_pt (hp2 : p ≠ 2) {x y : Generic.Closure K} (h : (Egen K).toAffine.Equation x y)
    (hψ : ((Egen K).preΨ p).eval x = 0) : p • pt x y h = 0 :=
  (Point.nsmul_some_eq_zero_iff_eval_prePsi (Egen K) (hprime.out.odd_of_ne_two hp2) _).2
    (by rwa [← preΨ_ofNat])

def tpt (hp2 : p ≠ 2) (x y : Generic.Closure K) (h : (Egen K).toAffine.Equation x y)
    (hψ : ((Egen K).preΨ p).eval x = 0) : Tor K p :=
  ⟨pt x y h, by
    rw [Submodule.mem_torsionBy_iff]
    show ((p : ℕ) : ℤ) • pt x y h = 0
    rw [natCast_zsmul]
    exact p_nsmul_pt hp2 h hψ⟩

theorem tpt_ne_zero (hp2 : p ≠ 2) (x y : Generic.Closure K) (h : (Egen K).toAffine.Equation x y)
    (hψ : ((Egen K).preΨ p).eval x = 0) : tpt hp2 x y h hψ ≠ 0 := fun e =>
  pt_ne_zero x y h (congrArg Subtype.val e)

@[scoped simp] theorem coe_tpt (hp2 : p ≠ 2) (x y : Generic.Closure K) (h : (Egen K).toAffine.Equation x y)
    (hψ : ((Egen K).preΨ p).eval x = 0) : (tpt hp2 x y h hψ : Pt K) = Point.some x y ((equation_iff_nonsingular ..).mp h) := rfl

theorem indepElt_eq_zero_of_inLine {A : Type*} [CommRing A] {W : WeierstrassCurve A} {n : ℕ}
    {x₀ x : A} (h : InLine W n x₀ x) : indepElt W n x₀ x = 0 := by
  obtain ⟨a, ha, ha', hx⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨ha, ha'⟩) (by rw [hx, sub_self])

theorem inLine_of_indepElt_eq_zero {A : Type*} [CommRing A] [IsDomain A] {W : WeierstrassCurve A}
    {n : ℕ} {x₀ x : A} (h : indepElt W n x₀ x = 0) : InLine W n x₀ x := by
  obtain ⟨a, ha, hx⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨a, (Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2, sub_eq_zero.mp hx⟩

theorem coe_zmod_smul (c : ZMod p) (t : Tor K p) : ((c • t : Tor K p) : Pt K) = (c.cast : ℤ) • (t : Pt K) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul]
  rfl

variable (hp2 : p ≠ 2)
include hp2

theorem indepElt_eq_zero_of_mk_eq {t₀ t : Tor K p} (ht₀ : t₀ ≠ 0) (ht : t ≠ 0)
    {x₀ y₀ x y : Generic.Closure K} {h₀ : (Egen K).toAffine.Nonsingular x₀ y₀}
    {h : (Egen K).toAffine.Nonsingular x y}
    (e₀ : (t₀ : Pt K) = Point.some x₀ y₀ h₀) (e : (t : Pt K) = Point.some x y h)
    (hmk : Projectivization.mk (ZMod p) t ht = Projectivization.mk (ZMod p) t₀ ht₀) :
    indepElt (Egen K) p x₀ x = 0 := by
  have hP₀ : p • Point.some x₀ y₀ h₀ = 0 := by
    have h2 := t₀.2
    rw [Submodule.mem_torsionBy_iff, e₀] at h2
    rw [← natCast_zsmul]
    exact h2
  rw [indepElt_eq_zero_iff_mem_zmultiples hp2 h₀ h hP₀, ← e, ← e₀]
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ ht ht₀).mp hmk
  rw [← ha, coe_zmod_smul]
  exact AddSubgroup.zsmul_mem_zmultiples _ _

theorem mk_eq_mk_of_inLine {t₀ t : Tor K p} (ht₀ : t₀ ≠ 0) (ht : t ≠ 0)
    {x₀ y₀ x y : Generic.Closure K} {h₀ : (Egen K).toAffine.Nonsingular x₀ y₀}
    {h : (Egen K).toAffine.Nonsingular x y}
    (e₀ : (t₀ : Pt K) = Point.some x₀ y₀ h₀) (e : (t : Pt K) = Point.some x y h)
    (hin : InLine (Egen K) p x₀ x) :
    Projectivization.mk (ZMod p) t ht = Projectivization.mk (ZMod p) t₀ ht₀ := by
  have hP₀ : p • Point.some x₀ y₀ h₀ = 0 := by
    have h2 := t₀.2
    rw [Submodule.mem_torsionBy_iff, e₀] at h2
    rw [← natCast_zsmul]
    exact h2
  have hmem := (indepElt_eq_zero_iff_mem_zmultiples hp2 h₀ h hP₀).mp (indepElt_eq_zero_of_inLine hin)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ ht ht₀).mpr ⟨(m : ZMod p), Subtype.ext ?_⟩
  rw [Int.cast_smul_eq_zsmul, Submodule.coe_smul, e₀, e, ← hm]

variable (K p)

local notation "LL" => Generic.FunctionField K
local notation "CC" => Generic.Closure K

omit hp2 in
theorem some_eq_some {x y x' y' : CC} {h : (Egen K).toAffine.Nonsingular x y}
    {h' : (Egen K).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx; subst hy; rfl

def galTor (γ : CC ≃ₐ[LL] CC) : Tor K p →+ Tor K p where
  toFun t := ⟨Point.map (γ : CC →ₐ[LL] CC) (t : Pt K), by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp t.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

omit hp2 hprime in
theorem coe_galTor (γ : CC ≃ₐ[LL] CC) (t : Tor K p) :
    (galTor K p γ t : Pt K) = Point.map (γ : CC →ₐ[LL] CC) (t : Pt K) := rfl

omit hp2 hprime in
theorem galTor_one (t : Tor K p) : galTor K p 1 t = t := by
  apply Subtype.ext
  obtain ⟨P, hP⟩ := t
  cases P <;> rfl

omit hp2 hprime in
theorem galTor_mul (γ δ : CC ≃ₐ[LL] CC) (t : Tor K p) :
    galTor K p (γ * δ) t = galTor K p γ (galTor K p δ t) := by
  apply Subtype.ext
  obtain ⟨P, hP⟩ := t
  cases P <;> rfl

def ρ (γ : CC ≃ₐ[LL] CC) : Tor K p ≃ₗ[ZMod p] Tor K p :=
  { AddMonoidHom.toZModLinearMap p (galTor K p γ) with
    invFun := galTor K p γ⁻¹
    left_inv := fun t => by
      show galTor K p γ⁻¹ (galTor K p γ t) = t
      rw [← galTor_mul, inv_mul_cancel, galTor_one]
    right_inv := fun t => by
      show galTor K p γ (galTor K p γ⁻¹ t) = t
      rw [← galTor_mul, mul_inv_cancel, galTor_one] }

omit hp2 in
theorem ρ_apply (γ : CC ≃ₐ[LL] CC) (t : Tor K p) : ρ K p γ t = galTor K p γ t := rfl

def ρHom : (CC ≃ₐ[LL] CC) →* (Tor K p ≃ₗ[ZMod p] Tor K p) where
  toFun := ρ K p
  map_one' := LinearEquiv.ext fun t => galTor_one K p t
  map_mul' γ δ := LinearEquiv.ext fun t => galTor_mul K p γ δ t

@[reducible] def lineAction : MulAction (CC ≃ₐ[LL] CC) (ℙ (ZMod p) (Tor K p)) :=
  MulAction.compHom _ (ρHom K p)

attribute [local instance] lineAction

omit hp2 in
theorem galTor_ne_zero (γ : CC ≃ₐ[LL] CC) {t : Tor K p} (ht : t ≠ 0) : galTor K p γ t ≠ 0 :=
  (ρ K p γ).map_ne_zero_iff.mpr ht

omit hp2 in
theorem smul_mk (γ : CC ≃ₐ[LL] CC) (t : Tor K p) (ht : t ≠ 0) :
    γ • Projectivization.mk (ZMod p) t ht =
      Projectivization.mk (ZMod p) (galTor K p γ t) (galTor_ne_zero K p γ ht) := rfl

theorem exists_smul_eq (hp : (p : K) ≠ 0) (D E : ℙ (ZMod p) (Tor K p)) :
    ∃ γ : CC ≃ₐ[LL] CC, γ • D = E := by
  induction D using Projectivization.ind with
  | h t ht =>
  induction E using Projectivization.ind with
  | h t' ht' =>
  obtain ⟨P, hP⟩ := t
  obtain ⟨P', hP'⟩ := t'
  rcases P with _ | ⟨x, y, hxy⟩
  · exact (ht (Subtype.ext rfl)).elim
  rcases P' with _ | ⟨x', y', hxy'⟩
  · exact (ht' (Subtype.ext rfl)).elim
  have hodd := hprime.out.odd_of_ne_two hp2
  have hψ : ((Generic.curve K).preΨ p).eval x = 0 := by
    rw [curve_eq_Egen, preΨ_ofNat]
    refine (Point.nsmul_some_eq_zero_iff_eval_prePsi (Egen K) hodd hxy).1 ?_
    rw [← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).mp hP
  have hψ' : ((Generic.curve K).preΨ p).eval x' = 0 := by
    rw [curve_eq_Egen, preΨ_ofNat]
    refine (Point.nsmul_some_eq_zero_iff_eval_prePsi (Egen K) hodd hxy').1 ?_
    rw [← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).mp hP'
  obtain ⟨σ, hσ⟩ := Generic.exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero hp2 hp hψ hψ'
  rw [curve_eq_Egen] at hσ
  refine ⟨σ, ?_⟩
  rw [smul_mk]
  symm
  exact mk_eq_mk_of_inLine hp2 (galTor_ne_zero K p σ ht) ht' rfl rfl hσ

variable (ζ : Kˣ) (hζ : ζ ^ p = 1)

def cs (a : ZMod p) : LevelPData (LaurentSeries K) := cuspData K p ζ ![a, 1] ![a + 1, 1]

omit hp2 in
theorem cuspShift_vec (x : ZMod p) : cuspShift p ![x, 1] = ![x + 1, 1] := by
  ext i
  fin_cases i <;> simp [cuspShift]

omit hp2 in
theorem cs_zero_eq : cs K p ζ 0 = cuspData K p ζ ![0, 1] ![1, 1] := by
  rw [cs, zero_add]

omit hp2 in
include hζ in

theorem isLevelPStructure_cs
    (hc : IsLevelPStructure (tateBase K p) p (cuspData K p ζ ![0, 1] ![1, 1])) (a : ZMod p) :
    IsLevelPStructure (tateBase K p) p (cs K p ζ a) := by
  have key : ∀ n : ℕ, IsLevelPStructure (tateBase K p) p
      (cuspData K p ζ ![(n : ZMod p), 1] ![(n : ZMod p) + 1, 1]) := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
      have h := ih.map (qTwist ζ)
      rw [tateBase_map_qTwist p ζ hζ, ModularCurve.cuspData_map_qTwist ζ hζ, cuspShift_vec,
        cuspShift_vec] at h
      push_cast
      exact h
  have h := key a.val
  rwa [ZMod.natCast_zmod_val] at h

def Dc (a : ZMod p) : LevelPData CC := D₃ p (cs K p ζ a)

variable (hp : (p : K) ≠ 0) (hc : IsLevelPStructure (tateBase K p) p (cuspData K p ζ ![0, 1] ![1, 1]))
include hζ hp hc

omit hp2 in
theorem isLevelPStructure_Dc (a : ZMod p) : IsLevelPStructure (Generic.curve K) p (Dc K p ζ a) :=
  isLevelPStructure_D₃ hp (isLevelPStructure_cs K p ζ hζ hc a)

omit hp2 in
theorem isLevelPStructure_Dc' (a : ZMod p) : IsLevelPStructure (Egen K) p (Dc K p ζ a) := by
  rw [← curve_eq_Egen]
  exact isLevelPStructure_Dc K p ζ hζ hp hc a

omit hp2 in
theorem Dc_map_σK (a : ZMod p) :
    (Dc K p ζ a).map (σK K p ζ hζ : CC →+* CC) = Dc K p ζ (a + 1) := by
  have h := D₃_map_σK K p ζ hζ hp (isLevelPStructure_cs K p ζ hζ hc a)
    (by rw [cuspShift_vec, cuspShift_vec]; exact isLevelPStructure_cs K p ζ hζ hc (a + 1))
  rw [cuspShift_vec, cuspShift_vec] at h
  exact h

def TP (a : ZMod p) : Tor K p :=
  tpt hp2 (Dc K p ζ a).xP (Dc K p ζ a).yP (isLevelPStructure_Dc' K p ζ hζ hp hc a).equation_P
    (isLevelPStructure_Dc' K p ζ hζ hp hc a).preΨ_P

theorem TP_ne_zero (a : ZMod p) : TP K p hp2 ζ hζ hp hc a ≠ 0 := tpt_ne_zero _ _ _ _ _

theorem galTor_σK_TP (a : ZMod p) :
    galTor K p (σK K p ζ hζ) (TP K p hp2 ζ hζ hp hc a) = TP K p hp2 ζ hζ hp hc (a + 1) := by
  apply Subtype.ext
  have h := Dc_map_σK K p ζ hζ hp hc a
  exact some_eq_some K (congrArg LevelPData.xP h) (congrArg LevelPData.yP h)

def ℓ (a : ZMod p) : ℙ (ZMod p) (Tor K p) :=
  Projectivization.mk (ZMod p) (TP K p hp2 ζ hζ hp hc a) (TP_ne_zero K p hp2 ζ hζ hp hc a)

theorem σK_smul_ℓ (a : ZMod p) : σK K p ζ hζ • ℓ K p hp2 ζ hζ hp hc a = ℓ K p hp2 ζ hζ hp hc (a + 1) := by
  rw [ℓ, smul_mk]
  exact (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ _ _).mpr ⟨1, by rw [one_smul, galTor_σK_TP]⟩

theorem ℓ_zero_ne : ℓ K p hp2 ζ hζ hp hc 0 ≠ ℓ K p hp2 ζ hζ hp hc (0 + 1) := by
  intro h
  have hD := isLevelPStructure_Dc' K p ζ hζ hp hc 0
  have h0 : indepElt (Egen K) p (Dc K p ζ 0).xP (Dc K p ζ 0).xQ = 0 :=
    indepElt_eq_zero_of_mk_eq hp2 (TP_ne_zero K p hp2 ζ hζ hp hc 0)
      (TP_ne_zero K p hp2 ζ hζ hp hc (0 + 1)) rfl rfl h.symm
  exact hD.isUnit_indepElt_PQ.ne_zero h0

end Torsion

end ModularCurve.QExpSplitField
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve.QExpSplitField"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "tateLaurent qExpand qExpand_C qExpand_injective indepElt InLine indepElt_map LevelPData LevelPData.map LevelPData.map_xP LevelPData.map_yP LevelPData.map_xQ LevelPData.map_yQ LevelPData.map_map LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ IsLevelPStructure KatzLevelPForm LevelPData.yQ LevelPData.xP LevelPData.yP LevelPData.ext LevelPData.xQ cuspData cuspShift algebraMap_laurentSeries_apply tateBase_map_qTwist isUnit_Δ_tateBase tateBase qTwist qTwist_single qTwist_one_apply qTwist_qTwist KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero algebraicIndependent_variableChange_tateLaurent cuspData_map_qTwist indepElt_eq_zero_iff_mem_zmultiples" namespace QExpSplitField end ModularCurve.QExpSplitField
p2m_open_scoped "ModularCurve" in
p2m_open "WeierstrassCurve~cusp" in open _root_.ModularCurve _root_.P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve ModularCurve.QExpSplitField WeierstrassCurve.Affine in
open scoped LinearAlgebra.Projectivization in

theorem ModularCurve.QExpSplitField.toFun_genericCurve_eq_zero
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) {k : ℤ}
    (hc : IsLevelPStructure (tateBase K p) p (cuspData K p ζ ![0, 1] ![1, 1]))
    (G : KatzLevelPForm K p k) (hG : G.DependsOnlyOnLines)
    (h0 : G.toFun (tateBase K p) (isUnit_Δ_tateBase K p) _ hc = 0)
    (D : LevelPData (Generic.Closure K)) (hD : IsLevelPStructure (Generic.curve K) p D) :
    G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D hD = 0 := by
  letI := decEqC K
  letI := modTor K p
  letI := lineAction K p
  have hprime : p.Prime := Fact.out

  have hDc0 := isLevelPStructure_Dc K p ζ hζ hp hc 0
  have hbase : G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) (Dc K p ζ 0) hDc0 = 0 := by
    have hcs0 := isLevelPStructure_cs K p ζ hζ hc 0
    have h0' : G.toFun (tateBase K p) (isUnit_Δ_tateBase K p) (cs K p ζ 0) hcs0 = 0 := by
      rw [← h0]
      exact toFun_congr G _ _ _ _ rfl (cs_zero_eq K p ζ)
    exact toFun_D₃_eq_zero hp G hcs0 h0'

  have hDE : IsLevelPStructure (Egen K) p D := by rw [← curve_eq_Egen]; exact hD
  let tP : Tor K p := tpt hp2 D.xP D.yP hDE.equation_P hDE.preΨ_P
  let tQ : Tor K p := tpt hp2 D.xQ D.yQ hDE.equation_Q hDE.preΨ_Q
  have htP : tP ≠ 0 := tpt_ne_zero _ _ _ _ _
  have htQ : tQ ≠ 0 := tpt_ne_zero _ _ _ _ _
  have hPQ : Projectivization.mk (ZMod p) tP htP ≠ Projectivization.mk (ZMod p) tQ htQ := by
    intro h
    have h0 : indepElt (Egen K) p D.xP D.xQ = 0 := indepElt_eq_zero_of_mk_eq hp2 htP htQ rfl rfl h.symm
    exact hDE.isUnit_indepElt_PQ.ne_zero h0

  haveI : Finite (ℙ (ZMod p) (Tor K p)) :=
    Nat.finite_of_card_ne_zero (by rw [card_lines K p hp]; exact Nat.succ_ne_zero _)
  have h01 : ℓ K p hp2 ζ hζ hp hc 0 ≠ ℓ K p hp2 ζ hζ hp hc 1 := by
    have h := ℓ_zero_ne K p hp2 ζ hζ hp hc
    rwa [zero_add] at h
  obtain ⟨γ, h1, h2⟩ := two_transitive (card_lines K p hp) (exists_smul_eq K p hp2 hp) (σK K p ζ hζ)
    (ℓ K p hp2 ζ hζ hp hc) (σK_smul_ℓ K p hp2 ζ hζ hp hc) h01 (ℓ_zero_ne K p hp2 ζ hζ hp hc) hPQ

  rw [ℓ, smul_mk] at h1 h2
  have hInP : InLine (Generic.curve K) p
      ((Dc K p ζ 0).map (γ : Generic.Closure K →+* Generic.Closure K)).xP D.xP := by
    rw [curve_eq_Egen]
    exact inLine_of_indepElt_eq_zero
      (indepElt_eq_zero_of_mk_eq hp2 (galTor_ne_zero K p γ (TP_ne_zero K p hp2 ζ hζ hp hc 0)) htP
        rfl rfl h1.symm)
  have hInQ : InLine (Generic.curve K) p
      ((Dc K p ζ 0).map (γ : Generic.Closure K →+* Generic.Closure K)).xQ D.xQ := by
    rw [curve_eq_Egen]
    exact inLine_of_indepElt_eq_zero
      (indepElt_eq_zero_of_mk_eq hp2 (galTor_ne_zero K p γ (TP_ne_zero K p hp2 ζ hζ hp hc (0 + 1)))
        htQ rfl rfl h2.symm)

  have hσD := isLevelPStructure_map_algEquiv γ hDc0
  have hval : G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K)
      ((Dc K p ζ 0).map (γ : Generic.Closure K →+* Generic.Closure K)) hσD = 0 := by
    rw [toFun_map_algEquiv G γ _ hDc0 hσD, hbase, map_zero]
  rw [hG (Generic.curve K) (Generic.isUnit_Δ_curve K) _ D hσD hD hInP hInQ, hval]

end
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve.QExpSplitField"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field.ModularCurve ModularCurve.QExpSplitField in
theorem solution
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase K p) p
      (ModularCurve.cuspData K p ζ ![0, 1] ![1, 1]))
    (G : ModularCurve.KatzLevelPForm K p k) (hG : G.DependsOnlyOnLines)
    (h0 : G.toFun (ModularCurve.tateBase K p) (ModularCurve.isUnit_Δ_tateBase K p) _ hc = 0) :
    G = 0 :=
  KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero hp2 hp G
    fun D hD => toFun_genericCurve_eq_zero hp2 hp ζ hζ hc G hG h0 D hD

end S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field
end P2MW
export P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field (solution)
