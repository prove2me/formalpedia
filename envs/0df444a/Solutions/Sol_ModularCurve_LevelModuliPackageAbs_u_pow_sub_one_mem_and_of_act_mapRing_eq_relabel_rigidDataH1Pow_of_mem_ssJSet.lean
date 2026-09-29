-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f3c45b5a-fdd1-5de7-ac90-2c3ce4753026

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
import Theorems.Thm_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
import Theorems.Thm_ModularCurve_IsGamma1Point_variableChange_eq_one_of_smul_eq_of_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] SubalgebraClass.toAlgebra
attribute [local instance 10001] AdicCompletion.instAlgebra

theorem PenRt1Guard.kguard
    {k : Type} [Field k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓk : ((ℓ : ℕ) : k) ≠ 0)
    (D : ModularCurve.LevelPData k) (hD : ModularCurve.IsGamma1Point W ℓ D)
    (C : WeierstrassCurve.VariableChange k) (hCW : C • W = W)
    (a : ℤ)
    (ha : ModularCurve.LevelRelabelling.toPoint W (D.variableChange C).xP (D.variableChange C).yP =
      a • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP) :
    (((a : ZMod ℓ) = 1 ∨ (a : ZMod ℓ) = -1) ∧
      ((a : ZMod ℓ) = 1 → C = 1) ∧
      ((a : ZMod ℓ) = -1 → ((C.u : kˣ) : k) = -1) ∧
      (((C.u : kˣ) : k) = 1 ∨ ((C.u : kˣ) : k) = -1)) := by
  classical
  have hℓP : ℓ.Prime := Fact.out
  have hℓ5 : 5 ≤ ℓ := by omega
  have hΔ : IsUnit W.Δ := W.isUnit_Δ
  have hℓu : IsUnit ((ℓ : ℕ) : k) := isUnit_iff_ne_zero.mpr hℓk

  have hP : W.toAffine.Nonsingular D.xP D.yP := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hD.equation_P
  have htoP : ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = WeierstrassCurve.Affine.Point.some D.xP D.yP hP := by
    unfold ModularCurve.LevelRelabelling.toPoint; rw [dif_pos hP]

  have hpre : (W.preΨ' ℓ).eval D.xP = 0 := by
    have h := hD.preΨ_P
    rwa [WeierstrassCurve.preΨ_ofNat] at h
  obtain ⟨hℓP0, h2P⟩ :=
    (WeierstrassCurve.Affine.Point.eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero W hℓk hP).mp hpre
  have hP0 : WeierstrassCurve.Affine.Point.some D.xP D.yP hP ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hP
  have hord : addOrderOf (WeierstrassCurve.Affine.Point.some D.xP D.yP hP) = ℓ :=
    (addOrderOf_eq_prime_iff.mpr ⟨hℓP0, hP0⟩)

  have heq' : W.toAffine.Equation (((C.u⁻¹ : kˣ) : k) ^ 2 * (D.xP - C.r))
      (((C.u⁻¹ : kˣ) : k) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t)) := by
    have h := ModularCurve.IsLevelPStructure.equation_variableChange_aux (W := W) C hD.equation_P
    rwa [hCW] at h
  have h' : W.toAffine.Nonsingular (((C.u⁻¹ : kˣ) : k) ^ 2 * (D.xP - C.r))
      (((C.u⁻¹ : kˣ) : k) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t)) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq'
  have htoP' : ModularCurve.LevelRelabelling.toPoint W (D.variableChange C).xP (D.variableChange C).yP =
      WeierstrassCurve.Affine.Point.some _ _ h' := by
    unfold ModularCurve.LevelRelabelling.toPoint
    simp only [ModularCurve.LevelPData.variableChange_xP, ModularCurve.LevelPData.variableChange_yP]
    rw [dif_pos h']
  have hn : WeierstrassCurve.Affine.Point.some _ _ h' = a • WeierstrassCurve.Affine.Point.some D.xP D.yP hP := by
    rw [← htoP', ha, htoP]

  have hpm := WeierstrassCurve.Affine.Point.some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
    p W C hCW ℓ hℓP hℓ12 hP hℓP0 h' a hn

  have cast_of : ∀ (e : ℤ), (a - e) • WeierstrassCurve.Affine.Point.some D.xP D.yP hP = 0 → (a : ZMod ℓ) = (e : ZMod ℓ) := by
    intro e he
    have hdvd : ((addOrderOf (WeierstrassCurve.Affine.Point.some D.xP D.yP hP) : ℕ) : ℤ) ∣ (a - e) :=
      (addOrderOf_dvd_iff_zsmul_eq_zero).mpr he
    rw [hord] at hdvd
    have h0 : ((a - e : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    rw [Int.cast_sub, sub_eq_zero] at h0
    exact h0

  let N : WeierstrassCurve.VariableChange k := ⟨-1, 0, -W.a₁, -W.a₃⟩
  have hNW : N • W = W := by
    ext <;> simp [N, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆] <;> ring
  have hDN : D.variableChange N = ⟨D.xP, W.toAffine.negY D.xP D.yP, D.xP, W.toAffine.negY D.xP D.yP⟩ := by
    apply ModularCurve.LevelPData.ext <;>
      simp [N, ModularCurve.LevelPData.variableChange_xP, ModularCurve.LevelPData.variableChange_yP,
        ModularCurve.LevelPData.variableChange_xQ, ModularCurve.LevelPData.variableChange_yQ, hD.xQ_eq, hD.yQ_eq,
        WeierstrassCurve.Affine.negY] <;> ring

  have vc_mul : ∀ (C₁ C₂ : WeierstrassCurve.VariableChange k) (D₀ : ModularCurve.LevelPData k),
      (D₀.variableChange C₁).variableChange C₂ = D₀.variableChange (C₂ * C₁) := by
    intro C₁ C₂ D₀
    apply ModularCurve.LevelPData.ext <;>
      simp [ModularCurve.LevelPData.variableChange_xP, ModularCurve.LevelPData.variableChange_yP,
        ModularCurve.LevelPData.variableChange_xQ, ModularCurve.LevelPData.variableChange_yQ,
        WeierstrassCurve.VariableChange.mul_def, mul_pow, Units.val_mul, Units.val_inv_eq_inv_val] <;> field_simp <;> ring
  have vc_one : ∀ (D₀ : ModularCurve.LevelPData k), D₀.variableChange 1 = D₀ := by
    intro D₀
    apply ModularCurve.LevelPData.ext <;>
      simp [ModularCurve.LevelPData.variableChange_xP, ModularCurve.LevelPData.variableChange_yP,
        ModularCurve.LevelPData.variableChange_xQ, ModularCurve.LevelPData.variableChange_yQ, WeierstrassCurve.VariableChange.one_def]

  have plus : WeierstrassCurve.Affine.Point.some _ _ h' = WeierstrassCurve.Affine.Point.some D.xP D.yP hP → C = 1 := by
    intro hfix
    have hc := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hfix
    have hCD : D.variableChange C = D := by
      apply ModularCurve.LevelPData.ext
      · simpa [ModularCurve.LevelPData.variableChange_xP] using hc.1
      · simpa [ModularCurve.LevelPData.variableChange_yP] using hc.2
      · rw [ModularCurve.LevelPData.variableChange_xQ, hD.xQ_eq]; simpa using hc.1
      · rw [ModularCurve.LevelPData.variableChange_yQ, hD.xQ_eq, hD.yQ_eq]; simpa using hc.2
    exact ModularCurve.IsGamma1Point.variableChange_eq_one_of_smul_eq_of_variableChange_eq ℓ hℓ5 hℓu W hΔ D hD C hCW hCD

  have minus : WeierstrassCurve.Affine.Point.some _ _ h' = -WeierstrassCurve.Affine.Point.some D.xP D.yP hP → C = N := by
    intro hfix
    rw [WeierstrassCurve.Affine.Point.neg_some] at hfix
    have hc := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hfix
    have hCD : D.variableChange C = D.variableChange N := by
      rw [hDN]
      apply ModularCurve.LevelPData.ext
      · simpa [ModularCurve.LevelPData.variableChange_xP] using hc.1
      · simpa [ModularCurve.LevelPData.variableChange_yP] using hc.2
      · rw [ModularCurve.LevelPData.variableChange_xQ, hD.xQ_eq]; simpa using hc.1
      · rw [ModularCurve.LevelPData.variableChange_yQ, hD.xQ_eq, hD.yQ_eq]; simpa using hc.2
    have hM : D.variableChange (N⁻¹ * C) = D := by
      rw [← vc_mul, hCD, vc_mul, inv_mul_cancel, vc_one]
    have hMW : (N⁻¹ * C) • W = W := by rw [mul_smul, hCW, ← hNW, smul_smul, inv_mul_cancel, one_smul, hNW]
    have h1 := ModularCurve.IsGamma1Point.variableChange_eq_one_of_smul_eq_of_variableChange_eq ℓ hℓ5 hℓu W hΔ D hD (N⁻¹ * C) hMW hM
    calc C = N * (N⁻¹ * C) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = N := by rw [h1, mul_one]
  have hNu : ((N.u : kˣ) : k) = -1 := by simp [N]

  rcases hpm with hfix | hfix
  · have ha1 : (a : ZMod ℓ) = 1 := by
      have := cast_of 1 (by rw [sub_smul, one_smul, ← hn, hfix, sub_self])
      simpa using this
    have hC1 := plus hfix
    refine ⟨Or.inl ha1, fun _ => hC1, fun hm1 => ?_, Or.inl (by rw [hC1, WeierstrassCurve.VariableChange.one_def]; simp)⟩

    exfalso
    have h2 : (2 : ZMod ℓ) = 0 := by linear_combination hm1 - ha1
    have h2' : ((2 : ℤ) : ZMod ℓ) = 0 := by exact_mod_cast h2
    have hd2 : (ℓ : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 ℓ).mp h2'
    have : ℓ ∣ 2 := by exact_mod_cast hd2
    have := Nat.le_of_dvd two_pos this
    omega
  · have ham1 : (a : ZMod ℓ) = -1 := by
      have := cast_of (-1) (by rw [sub_smul, neg_smul, one_smul, ← hn, hfix, sub_self])
      simpa using this
    have hCN := minus hfix
    refine ⟨Or.inr ham1, fun h1 => ?_, fun _ => by rw [hCN]; exact hNu, Or.inr (by rw [hCN]; exact hNu)⟩
    exfalso
    have h2 : (2 : ZMod ℓ) = 0 := by linear_combination ham1 - h1
    have h2' : ((2 : ℤ) : ZMod ℓ) = 0 := by exact_mod_cast h2
    have hd2 : (ℓ : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 ℓ).mp h2'
    have : ℓ ∣ 2 := by exact_mod_cast hd2
    have := Nat.le_of_dvd two_pos this
    omega

namespace LinScalars

theorem map_eq_one_of_mem_Gamma {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, h00, h01, h10, h11]

theorem mem_Gamma_of_map_eq_one {N : ℕ} (γ : SL(2, ℤ))
    (h : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1) :
    γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.map_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
    not_false_eq_true, Int.coe_castRingHom] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem levelPData_map_injective {T T' : Type} [CommRing T] [CommRing T'] (f : T →+* T') (hf : Function.Injective f)
    {D D' : ModularCurve.LevelPData T} (h : D.map f = D'.map f) : D = D' := by
  apply ModularCurve.LevelPData.ext
  · exact hf (by simpa using congrArg ModularCurve.LevelPData.xP h)
  · exact hf (by simpa using congrArg ModularCurve.LevelPData.yP h)
  · exact hf (by simpa using congrArg ModularCurve.LevelPData.xQ h)
  · exact hf (by simpa using congrArg ModularCurve.LevelPData.yQ h)

end LinScalars

open LinScalars in
set_option maxHeartbeats 4000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hℓA : IsUnit ((ℓg : ℕ) : A₀))
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

    [IsDomain R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)

    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (F : FormalGroup R) [F.IsComm]
    (hFW : F.toPowerSeries =
      (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)

    (hssJ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ιΩ : k →+* Ω),
      ιΩ (resR (ι P₀.j₀)) ∈ ModularCurve.ssJSet q Ω)

    (χP χQ : OriginChartRing ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R)
    (hP : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hBC : F.IsBaseChange resR F₀)
    (hDr : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (hmax : maximalIdeal R = Ideal.span {originParam χP, originParam χQ})
    (huniv : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁)

    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (ργ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
        (y y' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y'.level.2.1.xP y'.level.2.1.yP =
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y.level.2.1.xP y.level.2.1.yP →
        y'.level.2.1.xQ = y'.level.2.1.xP → y'.level.2.1.yQ = y'.level.2.1.yP →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y')
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R)

    (θ₀ : R →ₐ[W₀] R)
    (hcompl : ∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b))
    (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)

    (V : WeierstrassCurve.VariableChange R)
    (hΔ : IsUnit ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.Δ)
    (x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw R)
    (hact : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).act V ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x)) = x')
    (hcurve : x'.curve = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve)
    (hlev1 : x'.level.1 = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1)
    (hlev22 : x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ)
    [DecidableEq (FractionRing R)]

    (hlev21 : ModularCurve.LevelRelabelling.toPoint ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve).baseChange (FractionRing R))
        (algebraMap R (FractionRing R) x'.level.2.1.xP) (algebraMap R (FractionRing R) x'.level.2.1.yP) =
      (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
        ModularCurve.LevelRelabelling.toPoint ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve).baseChange (FractionRing R))
          (algebraMap R (FractionRing R) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.xP) (algebraMap R (FractionRing R) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.yP))
    (hlev21' : x'.level.2.1.xQ = x'.level.2.1.xP ∧ x'.level.2.1.yQ = x'.level.2.1.yP) :
    (((V.u : Rˣ) : R) ^ (q + 1) - 1 ∈ maximalIdeal R) ∧

    (((γ 1 1 : ℤ) : ZMod ℓg) = 1 → ((V.u : Rˣ) : R) - 1 ∈ maximalIdeal R) ∧

    (((γ 1 1 : ℤ) : ZMod ℓg) = -1 → ((V.u : Rˣ) : R) + 1 ∈ maximalIdeal R) ∧

    (γ ∈ CongruenceSubgroup.Gamma q → ((γ 1 1 : ℤ) : ZMod ℓg) ≠ 1 →
      (q = 2 → ((γ 1 1 : ℤ) : ZMod ℓg) ≠ -1) →
      ((V.u : Rˣ) : R) - 1 ∉ maximalIdeal R) := by
  classical
  haveI hℓgF : Fact ℓg.Prime := ⟨hℓg⟩

  let Rd := rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯
  let xR := Rd.mapRing ι x
  let E : WeierstrassCurve R := x.curve.map ι.toRingHom
  let D : ModularCurve.LevelPData R := xR.level.2.1
  let θA : R →ₐ[A₀] R := θ₀.restrictScalars A₀
  let g : Matrix (Fin 2) (Fin 2) ℤ := ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  have hEdef : xR.curve = E := rfl
  have hE : IsUnit E.Δ := by
    have h := xR.isUnit_Δ
    rw [hEdef] at h
    exact h
  have hDlev : ModularCurve.IsGamma1Point E ℓg D := by
    have h : ModularCurve.IsGamma1Point xR.curve ℓg D := xR.isLevel.1.2.1
    rw [hEdef] at h
    exact h
  have hresθ : resR.comp θA.toRingHom = resR := by
    ext r
    have h := hres r
    rw [← hkerR, RingHom.mem_ker, map_sub, sub_eq_zero] at h
    exact h
  have hc' : x'.curve = V • (E.map θA.toRingHom) := by rw [← hact]; rfl
  have h21' : x'.level.2.1 = (D.map θA.toRingHom).variableChange V := by rw [← hact]; rfl
  have hVE : V • (E.map θA.toRingHom) = E := hc'.symm.trans (hcurve.trans hEdef)

  let Vb : WeierstrassCurve.VariableChange k := V.map resR
  let Eb : WeierstrassCurve k := E.map resR
  let Db : ModularCurve.LevelPData k := D.map resR
  have hVbEb : Vb • Eb = Eb := by
    have h := congrArg (fun W : WeierstrassCurve R => W.map resR) hVE
    beta_reduce at h
    rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map, hresθ] at h
    exact h
  have hEb : IsUnit Eb.Δ := by rw [WeierstrassCurve.map_Δ]; exact hE.map resR
  haveI : Eb.IsElliptic := ⟨hEb⟩
  have hDb : ModularCurve.IsGamma1Point Eb ℓg Db := hDlev.map resR
  have hVbu : ((Vb.u : kˣ) : k) = resR ((V.u : Rˣ) : R) := by
    simp [Vb, WeierstrassCurve.VariableChange.map]
  have hred21 : x'.level.2.1.map resR = Db.variableChange Vb := by
    rw [h21', ModularCurve.LevelPData.map_variableChange, ModularCurve.LevelPData.map_map, hresθ]

  have h10 : ((g 1 0 : ℤ) : ZMod ℓg) = 0 := by
    have hM0 : ((g 1 0 : ℤ) : ZMod M') = 0 := by
      simpa using (CongruenceSubgroup.Gamma0_mem.mp hγ)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hM0 ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓgM') hM0
  have hdet : ((g 0 0 : ℤ) : ZMod ℓg) * ((g 1 1 : ℤ) : ZMod ℓg) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hd
    have hd' := congrArg (Int.cast : ℤ → ZMod ℓg) hd
    push_cast at hd'
    rw [h10, mul_zero, sub_zero] at hd'
    exact hd'
  have ha : ¬ ((ℓg : ℤ) ∣ g 0 0) := by
    intro h
    have h0 : ((g 0 0 : ℤ) : ZMod ℓg) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet

  obtain ⟨diam, hd1, hd2, hd3, -, -, -, -, -⟩ :=
    ModularCurve.LevelRelabelling.exists_natural_zsmul_gamma1Point A₀ ℓg (by omega) hℓA 𝒢 h𝒢 h𝒢O
  let Fr := FractionRing R
  let jR : R →ₐ[A₀] Fr := IsScalarTower.toAlgHom A₀ R Fr
  have hjR : jR.toRingHom = algebraMap R Fr := rfl
  have hjinj : Function.Injective (algebraMap R Fr) := IsFractionRing.injective R Fr
  have hEF : IsUnit (E.map (algebraMap R Fr)).Δ := by rw [WeierstrassCurve.map_Δ]; exact hE.map _
  haveI hEFell : (E.map (algebraMap R Fr)).IsElliptic := ⟨hEF⟩
  have hDF : ModularCurve.IsGamma1Point (E.map (algebraMap R Fr)) ℓg (D.map (algebraMap R Fr)) := hDlev.map _
  have hx'lev : ModularCurve.IsGamma1Point E ℓg x'.level.2.1 := by
    have h : ModularCurve.IsGamma1Point x'.curve ℓg x'.level.2.1 := x'.isLevel.1.2.1
    rw [hcurve, hEdef] at h
    exact h
  have hx'F : ModularCurve.IsGamma1Point (E.map (algebraMap R Fr)) ℓg (x'.level.2.1.map (algebraMap R Fr)) := hx'lev.map _
  let dR : ModularCurve.LevelPData R := diam R E (g 0 0) D
  have hdR : ModularCurve.IsGamma1Point E ℓg dR := hd2 R E hE (g 0 0) ha D hDlev
  have hdRF : ModularCurve.IsGamma1Point (E.map (algebraMap R Fr)) ℓg (dR.map (algebraMap R Fr)) := hdR.map _
  have hnat : diam Fr (E.map (algebraMap R Fr)) (g 0 0) (D.map (algebraMap R Fr)) = dR.map (algebraMap R Fr) := by
    have h := hd3 R Fr jR E hE (g 0 0) ha D hDlev
    rw [hjR] at h
    exact h

  have toPoint_some : ∀ (W : WeierstrassCurve Fr) [W.IsElliptic] (u v : Fr) (huv : W.toAffine.Equation u v),
      ModularCurve.LevelRelabelling.toPoint W u v =
        WeierstrassCurve.Affine.Point.some u v ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp huv) := by
    intro W _ u v huv
    unfold ModularCurve.LevelRelabelling.toPoint
    rw [dif_pos ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp huv)]
  have hbc : (xR.curve).baseChange (FractionRing R) = E.map (algebraMap R Fr) := rfl
  have hx'eq : x'.level.2.1.map (algebraMap R Fr) = dR.map (algebraMap R Fr) := by
    have h1 := hd1 Fr (E.map (algebraMap R Fr)) hEF (g 0 0) ha (D.map (algebraMap R Fr)) hDF
    rw [hnat] at h1

    have h2 : ModularCurve.LevelRelabelling.toPoint (E.map (algebraMap R Fr))
        (x'.level.2.1.map (algebraMap R Fr)).xP (x'.level.2.1.map (algebraMap R Fr)).yP =
        (g 0 0) • ModularCurve.LevelRelabelling.toPoint (E.map (algebraMap R Fr))
          (D.map (algebraMap R Fr)).xP (D.map (algebraMap R Fr)).yP := by
      first
        | exact hlev21
        | (simp only [hbc, ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP]; exact hlev21)
        | (simp [hbc, ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP] at hlev21 ⊢; exact hlev21)
    rw [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP] at h1
    have h3 : ModularCurve.LevelRelabelling.toPoint (E.map (algebraMap R Fr))
        (x'.level.2.1.map (algebraMap R Fr)).xP (x'.level.2.1.map (algebraMap R Fr)).yP =
        ModularCurve.LevelRelabelling.toPoint (E.map (algebraMap R Fr))
          (dR.map (algebraMap R Fr)).xP (dR.map (algebraMap R Fr)).yP := by
      rw [h2, ← h1, ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP]
    rw [toPoint_some _ _ _ hx'F.equation_P, toPoint_some _ _ _ hdRF.equation_P] at h3
    have h4 := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h3
    apply ModularCurve.LevelPData.ext
    · exact h4.1
    · exact h4.2
    · rw [hx'F.xQ_eq, hdRF.xQ_eq]; exact h4.1
    · rw [hx'F.yQ_eq, hdRF.yQ_eq]; exact h4.2
  have hx'R : x'.level.2.1 = dR := levelPData_map_injective (algebraMap R Fr) hjinj hx'eq

  letI : Algebra A₀ k := (resR.comp (algebraMap A₀ R)).toAlgebra
  let resA : R →ₐ[A₀] k := AlgHom.mk resR (fun _ => rfl)
  have hresA : resA.toRingHom = resR := rfl
  have hnatk : diam k Eb (g 0 0) Db = dR.map resR := by
    have h := hd3 R k resA E hE (g 0 0) ha D hDlev
    rw [hresA] at h
    exact h
  have hDbV : Db.variableChange Vb = diam k Eb (g 0 0) Db := by
    rw [hnatk, ← hred21, hx'R]
  have hrel : ModularCurve.LevelRelabelling.toPoint Eb (Db.variableChange Vb).xP (Db.variableChange Vb).yP =
      (g 0 0) • ModularCurve.LevelRelabelling.toPoint Eb Db.xP Db.yP := by
    rw [hDbV]
    exact hd1 k Eb hEb (g 0 0) ha Db hDb

  obtain ⟨hpm, hplus, hminus, hupm⟩ := PenRt1Guard.kguard (k := k) q Eb ℓg hℓg12 hℓk Db hDb Vb hVbEb (g 0 0) hrel

  have h00_of_11 : ∀ (e : ZMod ℓg), e * e = 1 → ((g 1 1 : ℤ) : ZMod ℓg) = e → ((g 0 0 : ℤ) : ZMod ℓg) = e := by
    intro e he h11
    rw [h11] at hdet
    calc ((g 0 0 : ℤ) : ZMod ℓg) = ((g 0 0 : ℤ) : ZMod ℓg) * (e * e) := by rw [he, mul_one]
      _ = (((g 0 0 : ℤ) : ZMod ℓg) * e) * e := by ring
      _ = e := by rw [hdet, one_mul]

  have hu_of_Vb1 : Vb = 1 → ((V.u : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro hVb1
    have : resR ((V.u : Rˣ) : R) = 1 := by
      rw [← hVbu, hVb1, WeierstrassCurve.VariableChange.one_def]; rfl
    rw [← hkerR, RingHom.mem_ker, map_sub, map_one, this, sub_self]
  have hu_of_neg : ((Vb.u : kˣ) : k) = -1 → ((V.u : Rˣ) : R) + 1 ∈ maximalIdeal R := by
    intro hm
    rw [hVbu] at hm
    rw [← hkerR, RingHom.mem_ker, map_add, map_one, hm, neg_add_cancel]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [← hkerR, RingHom.mem_ker, map_sub, map_one, map_pow, ← hVbu, sub_eq_zero]
    rcases hupm with hu | hu
    · rw [hu, one_pow]
    · rw [hu]
      rcases Nat.Prime.eq_two_or_odd (Fact.out : q.Prime) with hq2 | hqodd
      ·
        have h2 : (2 : k) = 0 := by
          have := CharP.cast_eq_zero k q; rw [hq2] at this; exact_mod_cast this
        have hm1 : (-1 : k) = 1 := by
          rw [neg_eq_iff_add_eq_zero, ← two_mul, mul_one]; exact h2
        rw [hm1, one_pow]
      · have hev : Even (q + 1) := by rcases Nat.odd_iff.mpr hqodd with ⟨m, hm⟩; exact ⟨m + 1, by omega⟩
        exact hev.neg_one_pow
  ·
    intro h11
    exact hu_of_Vb1 (hplus (h00_of_11 1 (one_mul 1) h11))
  ·
    intro h11
    exact hu_of_neg (hminus (h00_of_11 (-1) (by ring) h11))
  ·
    intro _hγq hne1 hcav hmem
    have h00ne1 : ((g 0 0 : ℤ) : ZMod ℓg) ≠ 1 := by
      intro h00
      apply hne1
      rw [h00, one_mul] at hdet
      exact hdet
    have h00m1 : ((g 0 0 : ℤ) : ZMod ℓg) = -1 := by
      rcases hpm with h | h
      · exact absurd h h00ne1
      · exact h
    have h11m1 : ((g 1 1 : ℤ) : ZMod ℓg) = -1 := by
      rw [h00m1] at hdet
      linear_combination (-1 : ZMod ℓg) * hdet
    have hum1 : ((Vb.u : kˣ) : k) = -1 := hminus h00m1
    have hres1 : resR ((V.u : Rˣ) : R) = 1 := by
      rw [← hkerR, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem; exact hmem
    rw [hVbu, hres1] at hum1

    have h2 : (2 : k) = 0 := by linear_combination hum1
    have hq2 : q = 2 := by
      have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff k q 2).mp (by exact_mod_cast h2)
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp hdvd
    exact hcav hq2 h11m1

end S_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_rigidDataH1Pow_of_mem_ssJSet (solution)
