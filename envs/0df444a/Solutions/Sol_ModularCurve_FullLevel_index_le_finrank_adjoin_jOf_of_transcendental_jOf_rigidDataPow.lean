-- Prove2me | solution 1 for ModularCurve.FullLevel.index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0bded465-a4ef-5a98-af0b-d09cd4a88617

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j
import Theorems.Thm_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed
import Theorems.Thm_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit
import Theorems.Thm_WeierstrassCurve_exists_variableChange_of_j_eq_of_sq
import Theorems.Thm_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

noncomputable section

namespace P2M
namespace IgusaDegLower

section Rigid

variable {A : Type} [CommRing A] (Lc : LevelComponent.{0} A)

abbrev Rg : RigidWeierstrassData.{0} A := Lc.toRigid

theorem rel_equivalence (T : Type) [CommRing T] [Algebra A T] :
    Equivalence ((Rg Lc).Rel (T := T)) where
  refl x := RigidWeierstrassData.Rel.refl _ x
  symm := by
    rintro x y ⟨C, rfl⟩
    refine ⟨C⁻¹, ?_⟩
    rw [← (Rg Lc).act_mul, inv_mul_cancel, (Rg Lc).act_one]
  trans := fun h h' => RigidWeierstrassData.Rel.trans _ h h'

theorem rel_of_mk_eq {T : Type} [CommRing T] [Algebra A T] {x y : (Rg Lc).Raw T}
    (h : (Quot.mk _ x : (Rg Lc).Pt T) = Quot.mk _ y) : (Rg Lc).Rel x y :=
  ((rel_equivalence Lc T).eqvGen_iff).1 (Quot.eqvGen_exact h)

theorem exists_stabilizer_of_mk_eq {T : Type} [CommRing T] [Algebra A T] {x y : Lc.Raw T}
    (h : (Quot.mk _ x : (Rg Lc).Pt T) = Quot.mk _ y) (hc : x.curve = y.curve) :
    ∃ C : WeierstrassCurve.VariableChange T, C • x.curve = x.curve ∧ y.level = Lc.act C x.level := by
  obtain ⟨C, hC⟩ := rel_of_mk_eq Lc h
  refine ⟨C, ?_, ?_⟩
  · have h1 : y.curve = C • x.curve := by rw [hC]; rfl
    rw [← h1, hc]
  · rw [hC]; rfl

end Rigid

section NegC

variable {F : Type} [Field F]

def negC (W : WeierstrassCurve F) : WeierstrassCurve.VariableChange F := ⟨-1, 0, -W.a₁, -W.a₃⟩

theorem negC_smul (W : WeierstrassCurve F) : negC W • W = W := by
  have hu : ((-1 : Fˣ)⁻¹ : Fˣ) = -1 := by rw [inv_neg, inv_one]
  ext
  · simp only [negC, WeierstrassCurve.variableChange_a₁, hu, Units.val_neg, Units.val_one]; ring
  · simp only [negC, WeierstrassCurve.variableChange_a₂, hu, Units.val_neg, Units.val_one]; ring
  · simp only [negC, WeierstrassCurve.variableChange_a₃, hu, Units.val_neg, Units.val_one]; ring
  · simp only [negC, WeierstrassCurve.variableChange_a₄, hu, Units.val_neg, Units.val_one]; ring
  · simp only [negC, WeierstrassCurve.variableChange_a₆, hu, Units.val_neg, Units.val_one]; ring

theorem negC_ne_one [CharZero F] (W : WeierstrassCurve F) : negC W ≠ 1 := by
  intro h
  have hu : (negC W).u = (1 : WeierstrassCurve.VariableChange F).u := by rw [h]
  have hu' : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := by
    have := congrArg (fun z : Fˣ => (z : F)) hu
    simpa [negC, WeierstrassCurve.VariableChange.one_def] using this
  rw [Units.val_neg, Units.val_one] at hu'
  have h2 : (2 : F) = 0 := by linear_combination -hu'
  exact two_ne_zero h2

theorem stabilizer_eq [IsAlgClosed F] [CharZero F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h0 : W.j ≠ 0) (h1728 : W.j ≠ 1728) (C : WeierstrassCurve.VariableChange F) (hC : C • W = W) :
    C = 1 ∨ C = negC W := by
  classical
  have hcard := WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth (K := F)
    (by rw [ringChar.eq F 0]; decide) (by rw [ringChar.eq F 0]; decide) W
  rw [ModularCurve.jWidth_of_ne h0 h1728, mul_one] at hcard
  rw [Nat.card_eq_two_iff' (⟨1, one_smul _ W⟩ : MulAction.stabilizer (WeierstrassCurve.VariableChange F) W)] at hcard
  obtain ⟨y, hy, huniq⟩ := hcard
  by_cases hC1 : C = 1
  · exact Or.inl hC1
  · right
    have e1 : (⟨C, hC⟩ : MulAction.stabilizer (WeierstrassCurve.VariableChange F) W) = y :=
      huniq ⟨C, hC⟩ (fun h => hC1 (congrArg Subtype.val h))
    have e2 : (⟨negC W, negC_smul W⟩ : MulAction.stabilizer (WeierstrassCurve.VariableChange F) W) = y :=
      huniq ⟨negC W, negC_smul W⟩ (fun h => negC_ne_one W (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)

end NegC

section Points

variable {k Ω : Type} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω] (E : WeierstrassCurve k) [E.IsElliptic]

theorem map_id' (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (AlgHom.id k Ω) P = P := by
  cases P <;> rfl

def autPt (σ : Ω ≃ₐ[k] Ω) : (E.baseChange Ω).toAffine.Point ≃+ (E.baseChange Ω).toAffine.Point where
  toFun := WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)
  invFun := WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω)
  left_inv P := by
    show WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω)
      (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P) = P
    rw [WeierstrassCurve.Affine.Point.map_map, AlgEquiv.symm_comp, map_id']
  right_inv P := by
    show WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)
      (WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω) P) = P
    rw [WeierstrassCurve.Affine.Point.map_map, AlgEquiv.comp_symm, map_id']
  map_add' P Q := map_add _ P Q

@[scoped simp] theorem autPt_apply (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    autPt E σ P = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P := rfl

theorem coe_autPt (σ : Ω ≃ₐ[k] Ω) :
    ((autPt E σ : (E.baseChange Ω).toAffine.Point ≃+ (E.baseChange Ω).toAffine.Point) :
      (E.baseChange Ω).toAffine.Point →+ (E.baseChange Ω).toAffine.Point) =
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) :=
  AddMonoidHom.ext fun _ => rfl

end Points

section Torsion

variable {V : Type} [AddCommGroup V]

theorem basis_of_addEquiv (N : ℕ) [NeZero N] (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ V (N : ℤ)) :
    N • ((e (1, 0) : Submodule.torsionBy ℤ V (N : ℤ)) : V) = 0 ∧
    N • ((e (0, 1) : Submodule.torsionBy ℤ V (N : ℤ)) : V) = 0 ∧
    (∀ a b : ℤ, a • ((e (1, 0) : Submodule.torsionBy ℤ V (N : ℤ)) : V) +
        b • ((e (0, 1) : Submodule.torsionBy ℤ V (N : ℤ)) : V) = 0 → (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) ∧
    (∀ v : V, N • v = 0 → ∃ a b : ℤ, v = a • ((e (1, 0) : Submodule.torsionBy ℤ V (N : ℤ)) : V) +
        b • ((e (0, 1) : Submodule.torsionBy ℤ V (N : ℤ)) : V)) := by
  have htor : ∀ t : Submodule.torsionBy ℤ V (N : ℤ), N • (t : V) = 0 := by
    intro t
    have := t.2
    rw [Submodule.mem_torsionBy_iff] at this
    rw [← natCast_zsmul]; simpa using this
  have hcomb : ∀ a b : ℤ, a • ((e (1, 0) : Submodule.torsionBy ℤ V (N : ℤ)) : V) +
      b • ((e (0, 1) : Submodule.torsionBy ℤ V (N : ℤ)) : V) = ((e ((a : ZMod N), (b : ZMod N)) : _) : V) := by
    intro a b
    have h1 : ((a : ZMod N), (b : ZMod N)) = a • ((1, 0) : ZMod N × ZMod N) + b • ((0, 1) : ZMod N × ZMod N) := by
      ext <;> simp
    rw [h1, map_add, map_zsmul, map_zsmul, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower]
  refine ⟨htor _, htor _, ?_, ?_⟩
  · intro a b hab
    rw [hcomb] at hab
    have h0 : e ((a : ZMod N), (b : ZMod N)) = 0 := Subtype.ext hab
    rw [map_eq_zero_iff e e.injective, Prod.mk_eq_zero] at h0
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a N).1 h0.1, (ZMod.intCast_zmod_eq_zero_iff_dvd b N).1 h0.2⟩
  · intro v hv
    have hv' : v ∈ Submodule.torsionBy ℤ V (N : ℤ) := by
      rw [Submodule.mem_torsionBy_iff]; simpa [← natCast_zsmul] using hv
    obtain ⟨⟨α, β⟩, hαβ⟩ := e.surjective ⟨v, hv'⟩
    refine ⟨(α.val : ℤ), (β.val : ℤ), ?_⟩
    rw [hcomb]
    have h2 : (((α.val : ℤ) : ZMod N), ((β.val : ℤ) : ZMod N)) = (α, β) := by
      ext <;> simp
    rw [h2, hαβ]

theorem nsmul_add_eq_zero_of_coprime {m n : ℕ} (P Q : V) (hP : m • P = 0) (hQ : n • Q = 0) :
    (m * n) • (P + Q) = 0 := by
  rw [nsmul_add, mul_comm m n, mul_nsmul', hP, nsmul_zero, mul_comm n m, mul_nsmul', hQ, nsmul_zero, add_zero]

theorem eq_zero_of_nsmul_eq_zero_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (X : V) (hm : m • X = 0)
    (hn : n • X = 0) : X = 0 := by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hmn : IsCoprime (m : ℤ) (n : ℤ))
  have h1 : (u * m + v * n) • X = X := by rw [huv, one_zsmul]
  rw [← h1, add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, hm, hn, zsmul_zero, zsmul_zero,
    add_zero]

theorem combined_basis {m n : ℕ} (hmn : Nat.Coprime m n) (P₁ P₂ Q₁ Q₂ : V)
    (hP₁ : m • P₁ = 0) (hP₂ : m • P₂ = 0)
    (hPi : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b)
    (hQ₁ : n • Q₁ = 0) (hQ₂ : n • Q₂ = 0)
    (hQi : ∀ a b : ℤ, a • Q₁ + b • Q₂ = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b) :
    (m * n) • (P₁ + Q₁) = 0 ∧ (m * n) • (P₂ + Q₂) = 0 ∧
    ∀ a b : ℤ, a • (P₁ + Q₁) + b • (P₂ + Q₂) = 0 → ((m * n : ℕ) : ℤ) ∣ a ∧ ((m * n : ℕ) : ℤ) ∣ b := by
  refine ⟨nsmul_add_eq_zero_of_coprime P₁ Q₁ hP₁ hQ₁, nsmul_add_eq_zero_of_coprime P₂ Q₂ hP₂ hQ₂, ?_⟩
  intro a b hab
  set X := a • P₁ + b • P₂ with hX
  set Y := a • Q₁ + b • Q₂ with hY
  have hXY : X + Y = 0 := by rw [hX, hY, ← hab]; simp only [zsmul_add]; abel
  have hmX : m • X = 0 := by
    rw [hX, nsmul_add, smul_comm, hP₁, smul_comm m b, hP₂, zsmul_zero, zsmul_zero, add_zero]
  have hnY : n • Y = 0 := by
    rw [hY, nsmul_add, smul_comm, hQ₁, smul_comm n b, hQ₂, zsmul_zero, zsmul_zero, add_zero]
  have hnX : n • X = 0 := by
    have : X = -Y := eq_neg_of_add_eq_zero_left hXY
    rw [this, smul_neg, hnY, neg_zero]
  have hX0 : X = 0 := eq_zero_of_nsmul_eq_zero_of_coprime hmn X hmX hnX
  have hY0 : Y = 0 := by rwa [hX0, zero_add] at hXY
  obtain ⟨hma, hmb⟩ := hPi a b (by rw [← hX]; exact hX0)
  obtain ⟨hna, hnb⟩ := hQi a b (by rw [← hY]; exact hY0)
  have hcopZ : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 hmn
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_mul]; exact hcopZ.mul_dvd hma hna
  · rw [Nat.cast_mul]; exact hcopZ.mul_dvd hmb hnb

end Torsion

section Descent

variable {A : Type} [CommRing A] {L : Type} [Field L] [Algebra A L]
  {T : Type} [Field T] [Algebra A T] [Algebra L T] [IsScalarTower A L T]
  {Ω : Type} [Field Ω] [Algebra T Ω] [Algebra A Ω] [IsScalarTower A T Ω]

variable (A) in

def toA (k : IntermediateField L T) (ψ : T →ₐ[k] Ω) : T →ₐ[A] Ω :=
  { ψ.toRingHom with
    commutes' := fun a => by
      show ψ (algebraMap A T a) = algebraMap A Ω a
      have h1 : algebraMap A T a = algebraMap (↥k) T (algebraMap L (↥k) (algebraMap A L a)) := by
        rw [← IsScalarTower.algebraMap_apply L (↥k) T, ← IsScalarTower.algebraMap_apply A L T]
      rw [h1, ψ.commutes, IsScalarTower.algebraMap_apply (↥k) T Ω, ← h1, ← IsScalarTower.algebraMap_apply A T Ω] }

@[scoped simp] theorem toA_apply (k : IntermediateField L T) (ψ : T →ₐ[k] Ω) (t : T) : toA A k ψ t = ψ t := rfl

variable (D : LevelModuliDatum.{0} A) (x : D.Pt T)

def conj (k : IntermediateField L T) : Set (D.Pt Ω) :=
  Set.range fun ψ : T →ₐ[k] Ω => D.map (toA A k ψ) x

theorem conj_finite (k : IntermediateField L T) [FiniteDimensional k T] : (conj D x k (Ω := Ω)).Finite :=
  Set.finite_range _

theorem ncard_conj_le [IsAlgClosed Ω] (k : IntermediateField L T) [FiniteDimensional k T] :
    (conj D x k (Ω := Ω)).ncard ≤ Module.finrank k T := by
  have h1 : (conj D x k (Ω := Ω)).ncard ≤ Nat.card (T →ₐ[k] Ω) := by
    rw [conj, ← Set.image_univ, ← Set.ncard_univ]
    exact Set.ncard_image_le Set.finite_univ
  have h2 : Nat.card (T →ₐ[k] Ω) = Field.finSepDegree k T := (Field.finSepDegree_eq_of_isAlgClosed k T Ω).symm
  rw [h2] at h1
  exact h1.trans (Field.finSepDegree_le_finrank k T)

end Descent

section Core

variable {A : Type} [CommRing A] (Lc : LevelComponent.{0} A)

def combine {P : Type} [AddCommGroup P] (t : ((P × P) × (P × P)) × AddSubgroup P) : P × P × AddSubgroup P :=
  (t.1.1.1 + t.1.2.1, t.1.1.2 + t.1.2.2, t.2)

theorem core
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (K k' Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field k'] [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [DecidableEq Ω] [Algebra K k'] [Algebra K Ω] [Algebra k' Ω] [IsScalarTower K k' Ω] [IsAlgClosure k' Ω]
    [Algebra A k'] [Algebra A Ω] [IsScalarTower A k' Ω]
    (E₀ : WeierstrassCurve k') [E₀.IsElliptic] (hE : Transcendental K E₀.j)
    (hgen : IntermediateField.adjoin K ({E₀.j} : Set k') = ⊤)
    (xΩ : (Rg Lc).Pt Ω) (hjx : (Rg Lc).jOf xΩ = algebraMap k' Ω E₀.j)
    (O : Set ((Rg Lc).Pt Ω)) (hO : O.Finite)
    (hmemO : ∀ σ : Ω ≃ₐ[k'] Ω, (Rg Lc).map ((σ : Ω →ₐ[k'] Ω).restrictScalars A) xΩ ∈ O)
    (hΘ : ∃ Θ : Lc.obj Ω →
        (((E₀.baseChange Ω).toAffine.Point × (E₀.baseChange Ω).toAffine.Point) ×
          ((E₀.baseChange Ω).toAffine.Point × (E₀.baseChange Ω).toAffine.Point)) ×
          AddSubgroup (E₀.baseChange Ω).toAffine.Point,
      ∀ β : Lc.obj Ω, Lc.IsLevel (E₀.baseChange Ω) β →
        (ℓ • (Θ β).1.1.1 = 0 ∧ ℓ • (Θ β).1.1.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.1.1 + b • (Θ β).1.1.2 = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b) ∧
        (q • (Θ β).1.2.1 = 0 ∧ q • (Θ β).1.2.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.2.1 + b • (Θ β).1.2.2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
        (IsAddCyclic (Θ β).2 ∧ Nat.card (Θ β).2 = M') ∧
        (∀ σ : Ω ≃ₐ[k'] Ω,
          Θ (Lc.map ((σ : Ω →ₐ[k'] Ω).restrictScalars A) β) =
            (((WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k'] Ω) (Θ β).1.1.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k'] Ω) (Θ β).1.1.2),
              (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k'] Ω) (Θ β).1.2.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k'] Ω) (Θ β).1.2.2)),
              ((Θ β).2).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k'] Ω))))) :
    2 * (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ 2 * O.ncard := by

  haveI hE₀Ωell : (E₀.baseChange Ω).IsElliptic := by
    show (E₀.map (algebraMap k' Ω)).IsElliptic; infer_instance
  have hE₀Ωj : (E₀.baseChange Ω).j = algebraMap k' Ω E₀.j := E₀.map_j _
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  have hjt : Transcendental K (algebraMap k' Ω E₀.j) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective k' Ω)).2 hE
  have hj0 : (E₀.baseChange Ω).j ≠ 0 := by
    rw [hE₀Ωj]; intro h; exact hjt (by rw [h]; exact isAlgebraic_zero)
  have hj1728 : (E₀.baseChange Ω).j ≠ 1728 := by
    rw [hE₀Ωj]; intro h; exact hjt (by rw [h]; exact isAlgebraic_nat 1728)

  obtain ⟨w, hw⟩ := Quot.exists_rep xΩ
  haveI hwE : (w.curve).IsElliptic := ⟨w.isUnit_Δ⟩
  have hjw : w.curve.j = (E₀.baseChange Ω).j := by
    rw [hE₀Ωj, ← hjx, ← hw]
    exact (WeierstrassCurve.jOfUnit_eq_j w.curve w.isUnit_Δ).symm
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w.curve.c₆ * (E₀.baseChange Ω).c₄ / ((E₀.baseChange Ω).c₆ * w.curve.c₄)) two_pos
  obtain ⟨Cw, hCw⟩ := WeierstrassCurve.exists_variableChange_of_j_eq_of_sq (F := Ω) two_ne_zero three_ne_zero
    w.curve (E₀.baseChange Ω) hjw (by rw [hjw]; exact hj0) (by rw [hjw]; exact hj1728) hs
  set w₀ : Lc.Raw Ω := (Rg Lc).act Cw w with hw₀
  have hw₀c : w₀.curve = (E₀.baseChange Ω) := hCw
  have hxw₀ : (Quot.mk _ w₀ : (Rg Lc).Pt Ω) = xΩ := by
    rw [← hw]; exact (Quot.sound ⟨Cw, rfl⟩).symm
  set β : Lc.obj Ω := w₀.level with hβdef
  have hβ : Lc.IsLevel (E₀.baseChange Ω) β := by rw [← hw₀c]; exact w₀.isLevel

  let σA : (Ω ≃ₐ[k'] Ω) → (Ω →ₐ[A] Ω) := fun σ => (σ : Ω →ₐ[k'] Ω).restrictScalars A
  let y : (Ω ≃ₐ[k'] Ω) → Lc.Raw Ω := fun σ => (Rg Lc).mapRing (σA σ) w₀
  have hyc : ∀ σ, (y σ).curve = (E₀.baseChange Ω) := by
    intro σ
    show (w₀.curve).map (σA σ).toRingHom = (E₀.baseChange Ω)
    rw [hw₀c, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    congr 1
    exact (σ : Ω →ₐ[k'] Ω).comp_algebraMap
  have hyl : ∀ σ, (y σ).level = Lc.map (σA σ) β := fun σ => rfl
  have hymk : ∀ σ, (Quot.mk _ (y σ) : (Rg Lc).Pt Ω) = (Rg Lc).map (σA σ) xΩ := by
    intro σ; rw [← hxw₀]; rfl
  have hyLevel : ∀ σ, Lc.IsLevel (E₀.baseChange Ω) (Lc.map (σA σ) β) := by
    intro σ; rw [← hyl, ← hyc σ]; exact (y σ).isLevel

  have hfib : ∀ σ τ, (Rg Lc).map (σA σ) xΩ = (Rg Lc).map (σA τ) xΩ →
      Lc.map (σA τ) β = Lc.map (σA σ) β ∨ Lc.map (σA τ) β = Lc.act (negC (E₀.baseChange Ω)) (Lc.map (σA σ) β) := by
    intro σ τ hστ
    rw [← hymk, ← hymk] at hστ
    obtain ⟨C, hC1, hC2⟩ := exists_stabilizer_of_mk_eq Lc hστ ((hyc σ).trans (hyc τ).symm)
    rw [hyc σ] at hC1
    rcases stabilizer_eq (E₀.baseChange Ω) hj0 hj1728 C hC1 with h | h
    · left; rw [← hyl, ← hyl, hC2, h, Lc.act_one]
    · right; rw [← hyl, ← hyl, hC2, h]

  obtain ⟨Θ, hΘ⟩ := hΘ
  let Θc : Lc.obj Ω → (E₀.baseChange Ω).toAffine.Point × (E₀.baseChange Ω).toAffine.Point ×
      AddSubgroup (E₀.baseChange Ω).toAffine.Point := fun b => combine (Θ b)

  set O' : Set ((Rg Lc).Pt Ω) := Set.range fun σ : Ω ≃ₐ[k'] Ω => (Rg Lc).map (σA σ) xΩ with hO'
  have hO'O : O' ⊆ O := by rintro _ ⟨σ, rfl⟩; exact hmemO σ
  have hO'fin : O'.Finite := hO.subset hO'O
  set Th : Set ((E₀.baseChange Ω).toAffine.Point × (E₀.baseChange Ω).toAffine.Point ×
      AddSubgroup (E₀.baseChange Ω).toAffine.Point) := Set.range fun σ : Ω ≃ₐ[k'] Ω => Θc (Lc.map (σA σ) β) with hTh
  haveI : Nonempty (Ω ≃ₐ[k'] Ω) := ⟨AlgEquiv.refl⟩
  let fΓ : (Ω ≃ₐ[k'] Ω) → (Rg Lc).Pt Ω := fun σ => (Rg Lc).map (σA σ) xΩ
  let sec : (Rg Lc).Pt Ω → (Ω ≃ₐ[k'] Ω) := Function.invFun fΓ
  have hsec : ∀ σ, fΓ (sec (fΓ σ)) = fΓ σ := fun σ => Function.invFun_eq (f := fΓ) ⟨σ, rfl⟩
  set img₁ := (fun o => Θc (Lc.map (σA (sec o)) β)) '' O' with himg₁
  set img₂ := (fun o => Θc (Lc.act (negC (E₀.baseChange Ω)) (Lc.map (σA (sec o)) β))) '' O' with himg₂
  have hThsub : Th ⊆ img₁ ∪ img₂ := by
    rintro _ ⟨σ, rfl⟩
    have ho : (Rg Lc).map (σA σ) xΩ ∈ O' := ⟨σ, rfl⟩
    rcases hfib (sec ((Rg Lc).map (σA σ) xΩ)) σ (hsec σ) with h | h
    · left; exact ⟨_, ho, by simp only [h]⟩
    · right; exact ⟨_, ho, by simp only [h]⟩
  have hThfin : (img₁ ∪ img₂).Finite := (hO'fin.image _).union (hO'fin.image _)
  have hTh_le : Th.ncard ≤ 2 * O.ncard := by
    calc Th.ncard ≤ (img₁ ∪ img₂).ncard := Set.ncard_le_ncard hThsub hThfin
      _ ≤ img₁.ncard + img₂.ncard := Set.ncard_union_le _ _
      _ ≤ O'.ncard + O'.ncard := Nat.add_le_add (Set.ncard_image_le hO'fin) (Set.ncard_image_le hO'fin)
      _ ≤ O.ncard + O.ncard := Nat.add_le_add (Set.ncard_le_ncard hO'O hO) (Set.ncard_le_ncard hO'O hO)
      _ = 2 * O.ncard := by ring

  obtain ⟨⟨hP₁, hP₂, hPi⟩, ⟨hQ₁, hQ₂, hQi⟩, ⟨hCcyc, hCcard⟩, hGal⟩ := hΘ β hβ
  have hcopℓq : Nat.Coprime ℓ q := (Nat.coprime_primes (Fact.out) (Fact.out)).2 hℓq
  obtain ⟨hPt₁, hPt₂, hPti⟩ := combined_basis hcopℓq (Θ β).1.1.1 (Θ β).1.1.2 (Θ β).1.2.1 (Θ β).1.2.2
    hP₁ hP₂ hPi hQ₁ hQ₂ hQi

  set N : ℕ := q * ℓ * M' with hN
  haveI : NeZero N := ⟨by rw [hN]; exact mul_ne_zero (mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero) (NeZero.ne M')⟩
  have hNΩ : ((N : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNK : ((N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) E₀ (n := N) hNΩ
  obtain ⟨hB₁, hB₂, hBi, hBs⟩ := basis_of_addEquiv N e

  set G : Set ((E₀.baseChange Ω).toAffine.Point ≃+ (E₀.baseChange Ω).toAffine.Point) :=
    Set.range fun σ : Ω ≃ₐ[k'] Ω => autPt E₀ σ with hG
  have hGsl : ∀ a b c d : ℤ, ((q * ℓ * M' : ℕ) : ℤ) ∣ a * d - b * c - 1 →
      ∃ g ∈ G, g ((e (1, 0) : Submodule.torsionBy ℤ _ (N : ℤ)) : (E₀.baseChange Ω).toAffine.Point) =
          a • ((e (1, 0) : Submodule.torsionBy ℤ _ (N : ℤ)) : (E₀.baseChange Ω).toAffine.Point) +
          c • ((e (0, 1) : Submodule.torsionBy ℤ _ (N : ℤ)) : (E₀.baseChange Ω).toAffine.Point) ∧
        g ((e (0, 1) : Submodule.torsionBy ℤ _ (N : ℤ)) : (E₀.baseChange Ω).toAffine.Point) =
          b • ((e (1, 0) : Submodule.torsionBy ℤ _ (N : ℤ)) : (E₀.baseChange Ω).toAffine.Point) +
          d • ((e (0, 1) : Submodule.torsionBy ℤ _ (N : ℤ)) : (E₀.baseChange Ω).toAffine.Point) := by
    intro a b c d hdet
    obtain ⟨σ, h1, h2⟩ := WeierstrassCurve.exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j K N hNK k' Ω E₀
      hE hgen _ _ hB₁ hB₂ hBi a b c d hdet
    exact ⟨autPt E₀ σ, ⟨σ, rfl⟩, h1, h2⟩

  have hN₀ : 3 ≤ q * ℓ := le_trans hℓ3 (Nat.le_mul_of_pos_left ℓ (by omega))
  have hcop : Nat.Coprime (q * ℓ) M' :=
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hqM') ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hℓM')
  have hcount := ModularCurve.FullLevel.two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit (q * ℓ) hN₀ M' hcop
    (E₀.baseChange Ω).toAffine.Point _ _ hB₁ hB₂ hBi hBs _ _
    (by rw [mul_comm]; exact hPt₁) (by rw [mul_comm]; exact hPt₂)
    (fun a b hab => by
      obtain ⟨ha, hb⟩ := hPti a b hab
      rw [mul_comm] at ha hb; exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩)
    (Θ β).2 hCcyc hCcard G hGsl

  have horb : {t : (E₀.baseChange Ω).toAffine.Point × (E₀.baseChange Ω).toAffine.Point ×
      AddSubgroup (E₀.baseChange Ω).toAffine.Point |
      ∃ g ∈ G, t = (g ((Θ β).1.1.1 + (Θ β).1.2.1), g ((Θ β).1.1.2 + (Θ β).1.2.2),
        ((Θ β).2).map (g : (E₀.baseChange Ω).toAffine.Point →+ (E₀.baseChange Ω).toAffine.Point))} ⊆ Th := by
    rintro t ⟨g, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    show combine (Θ (Lc.map (σA σ) β)) = _
    rw [hGal σ, combine]
    simp only [autPt_apply, map_add, coe_autPt]
  have hThfin' : Th.Finite := hThfin.subset hThsub
  calc 2 * (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
          Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ _ := hcount
    _ ≤ Th.ncard := Set.ncard_le_ncard horb hThfin'
    _ ≤ 2 * O.ncard := hTh_le

end Core

section Main

variable {A : Type} [CommRing A] (Lc : LevelComponent.{0} A)

theorem main
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra A L]
    (T : Type) [Field T] [Algebra A T] [Algebra L T] [IsScalarTower A L T]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω]
    [Algebra T Ω] [Algebra A Ω] [Algebra L Ω] [IsScalarTower A T Ω] [IsScalarTower L T Ω] [IsScalarTower A L Ω]
    [Algebra.IsAlgebraic T Ω]
    (hread : ∀ (K₀ : Type) [Field K₀] [Algebra A K₀] [Algebra K₀ Ω] [IsScalarTower A K₀ Ω]
        (E : WeierstrassCurve K₀) [E.IsElliptic],
      ∃ Θ : Lc.obj Ω →
        (((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point) ×
          ((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point)) ×
          AddSubgroup (E.baseChange Ω).toAffine.Point,
      ∀ β : Lc.obj Ω, Lc.IsLevel (E.baseChange Ω) β →
        (ℓ • (Θ β).1.1.1 = 0 ∧ ℓ • (Θ β).1.1.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.1.1 + b • (Θ β).1.1.2 = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b) ∧
        (q • (Θ β).1.2.1 = 0 ∧ q • (Θ β).1.2.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.2.1 + b • (Θ β).1.2.2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
        (IsAddCyclic (Θ β).2 ∧ Nat.card (Θ β).2 = M') ∧
        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (Lc.map ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) β) =
            (((WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1.2),
              (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.2)),
              ((Θ β).2).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)))))
    (x : (Rg Lc).Pt T) (hx : Transcendental L ((Rg Lc).jOf x))
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin L ({(Rg Lc).jOf x} : Set T)) T) :
    (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      Module.finrank ↥(IntermediateField.adjoin L ({(Rg Lc).jOf x} : Set T)) T := by
  classical
  haveI := hfin
  set j : T := (Rg Lc).jOf x with hjdef
  set k : IntermediateField L T := IntermediateField.adjoin L ({j} : Set T) with hkdef
  let ι : T →ₐ[A] Ω := IsScalarTower.toAlgHom A T Ω
  have hι : ∀ t, ι t = algebraMap T Ω t := fun _ => rfl
  set jΩ : Ω := algebraMap T Ω j with hjΩdef
  set xΩ : (Rg Lc).Pt Ω := (Rg Lc).map ι x with hxΩdef
  have hjxΩ : (Rg Lc).jOf xΩ = jΩ := (Rg Lc).toLevelModuliDatum.jOf_map ι x

  have hjΩ : Transcendental L jΩ := (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective T Ω)).2 hx
  set Kb : IntermediateField L Ω := algebraicClosure L Ω with hKbdef
  haveI : IsAlgClosed Kb := IsAlgClosure.isAlgClosed L (K := Kb)
  haveI : CharZero Kb := ⟨fun a b h => Nat.cast_injective (R := Ω) (by
    have := congrArg (algebraMap Kb Ω) h; simpa only [map_natCast] using this)⟩
  have hjK : Transcendental Kb jΩ := (Algebra.IsAlgebraic.transcendental_iff L Kb).1 hjΩ

  set k' : IntermediateField Kb Ω := IntermediateField.adjoin Kb ({jΩ} : Set Ω) with hk'def
  have hjmem : jΩ ∈ k' := IntermediateField.subset_adjoin _ _ (Set.mem_singleton jΩ)
  set jk : k' := ⟨jΩ, hjmem⟩ with hjkdef
  have hLmem : ∀ l : L, algebraMap L Ω l ∈ k' := by
    intro l
    have h1 : algebraMap L Ω l ∈ Kb := IntermediateField.algebraMap_mem Kb l
    exact IntermediateField.algebraMap_mem k' (⟨algebraMap L Ω l, h1⟩ : Kb)

  have hAmem : ∀ a : A, algebraMap A Ω a ∈ k' := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L Ω]
    exact hLmem _
  letI algAk' : Algebra A k' := ((algebraMap A Ω).codRestrict k' hAmem).toAlgebra
  haveI : IsScalarTower A k' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hkmem : ∀ z : k, algebraMap T Ω (z : T) ∈ k' := by
    intro z
    refine IntermediateField.adjoin_induction (F := L) (s := ({j} : Set T))
      (p := fun t _ => algebraMap T Ω t ∈ k') ?_ ?_ ?_ ?_ ?_ z.2
    · intro t ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]; exact hjmem
    · intro l
      rw [← IsScalarTower.algebraMap_apply L T Ω]
      exact hLmem l
    · intro t t' _ _ ht ht'
      rw [map_add]; exact add_mem ht ht'
    · intro t _ ht
      rw [map_inv₀]; exact inv_mem ht
    · intro t t' _ _ ht ht'
      rw [map_mul]; exact mul_mem ht ht'

  haveI : Algebra.IsAlgebraic k T := inferInstance
  have hkΩ : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.trans k T Ω
  let φ₀ : k →+* k' := ((algebraMap T Ω).comp (algebraMap k T)).codRestrict k' (fun z => hkmem z)
  haveI : IsAlgClosure k' Ω := by
    letI : Algebra k k' := φ₀.toAlgebra
    haveI : IsScalarTower k k' Ω :=
      IsScalarTower.of_algebraMap_eq (fun z => IsScalarTower.algebraMap_apply k T Ω z)
    haveI : Algebra.IsAlgebraic k' Ω := ⟨fun ω => (hkΩ.isAlgebraic ω).tower_top (L := k')⟩
    exact ⟨inferInstance, inferInstance⟩

  set E₀ : WeierstrassCurve k' := WeierstrassCurve.ofJ jk with hE₀def
  have hE₀j : E₀.j = jk := WeierstrassCurve.ofJ_j jk
  have hE : Transcendental Kb E₀.j := by
    rw [hE₀j]
    exact (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective k' Ω)).1 hjK
  have hgen : IntermediateField.adjoin Kb ({E₀.j} : Set k') = ⊤ := by
    rw [hE₀j]
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
  have hjx' : (Rg Lc).jOf xΩ = algebraMap k' Ω E₀.j := by rw [hE₀j, hjxΩ]; rfl

  have hOfin : (conj (Rg Lc).toLevelModuliDatum x k (Ω := Ω)).Finite := conj_finite (Rg Lc).toLevelModuliDatum x k
  have hOle : (conj (Rg Lc).toLevelModuliDatum x k (Ω := Ω)).ncard ≤ Module.finrank k T :=
    ncard_conj_le (Rg Lc).toLevelModuliDatum x k
  have hmemO : ∀ σ : Ω ≃ₐ[k'] Ω,
      (Rg Lc).map ((σ : Ω →ₐ[k'] Ω).restrictScalars A) xΩ ∈ conj (Rg Lc).toLevelModuliDatum x k (Ω := Ω) := by
    intro σ
    have hfix : ∀ z : k, σ (algebraMap T Ω (z : T)) = algebraMap T Ω (z : T) := fun z =>
      σ.commutes (⟨_, hkmem z⟩ : k')
    let ψ : T →ₐ[k] Ω :=
      { (((σ : Ω →ₐ[k'] Ω).restrictScalars A).comp ι).toRingHom with
        commutes' := fun z => by
          show σ (ι (algebraMap k T z)) = algebraMap k Ω z
          rw [hι, IsScalarTower.algebraMap_apply k T Ω]
          exact hfix z }
    refine ⟨ψ, ?_⟩
    exact (Rg Lc).toLevelModuliDatum.map_comp ι ((σ : Ω →ₐ[k'] Ω).restrictScalars A) x
  have hcore := core Lc q M' hqM' ℓ hℓ3 hℓq hℓM' Kb k' Ω E₀ hE hgen xΩ hjx' _ hOfin hmemO (hread k' E₀)
  have h2 : 2 * (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
      Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ 2 * Module.finrank k T :=
    hcore.trans (Nat.mul_le_mul_left 2 hOle)
  omega

end Main

end P2M.IgusaDegLower
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow.P2M P2MW.S_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow.P2M.IgusaDegLower"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow.P2M"

open P2M.IgusaDegLower in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [Algebra A L]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (T : Type) [Field T] [Algebra A T] [Algebra L T] [IsScalarTower A L T]
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T)
    (hx : Transcendental L ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x))
    (hfin : FiniteDimensional
      ↥(IntermediateField.adjoin L ({(rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x} : Set T)) T) :
    (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      Module.finrank ↥(IntermediateField.adjoin L ({(rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x} : Set T)) T := by
  classical
  haveI : CharZero T := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective L T)
  exact main ((ModularCurve.gamma0PowComponent A M' hM).prod
      ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯)))
    q M' hqM' ℓ hℓ3 hℓq hℓM' L T (AlgebraicClosure T)
    (fun K₀ _ _ _ _ E _ =>
      ModularCurve.FullLevel.exists_levelReading_baseChange_of_isAlgClosed q M' ℓ hℓ3 A hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO
        (AlgebraicClosure T) K₀ E)
    x hx hfin

end
end S_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow
end P2MW
export P2MW.S_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow (solution)
