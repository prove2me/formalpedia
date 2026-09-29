-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1ea3b5cf-56dc-535e-84ba-dfdcc928815c

import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

namespace RPBAux

variable {A : Type} [CommRing A]

theorem map_injective_of_injective (D : LevelModuliDatum A) (P₀ : LevelModuliPackageAbs A D)
    {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (hf : Function.Injective f) (p₁ p₂ : D.Pt T) (h : D.map f p₁ = D.map f p₂) : p₁ = p₂ := by
  have hc : ∀ p : D.Pt T, f.comp (P₀.classify p) = P₀.classify (D.map f p) := fun p =>
    P₀.classify_unique _ _ (by rw [D.map_comp, P₀.map_classify])
  have hcomp : f.comp (P₀.classify p₁) = f.comp (P₀.classify p₂) := by rw [hc, hc, h]
  have hcl : P₀.classify p₁ = P₀.classify p₂ := by
    refine AlgHom.ext fun b => hf ?_
    have := congrArg (fun φ : P₀.B₀ →ₐ[A] T' => φ b) hcomp
    simpa only [AlgHom.comp_apply] using this
  rw [← P₀.map_classify p₁, hcl, P₀.map_classify]

theorem exists_act_eq_of_mk_eq (Rd : RigidWeierstrassData A) {T : Type} [CommRing T] [Algebra A T]
    (y z : Rd.Raw T) (h : (Quot.mk _ y : Rd.Pt T) = Quot.mk _ z) :
    ∃ C : WeierstrassCurve.VariableChange T, Rd.act C y = z := by
  have key : ∀ w w' : Rd.Raw T, Rd.Rel w w' →
      ((∃ C : WeierstrassCurve.VariableChange T, Rd.act C y = w) ↔
        (∃ C : WeierstrassCurve.VariableChange T, Rd.act C y = w')) := by
    rintro w w' ⟨C', rfl⟩
    constructor
    · rintro ⟨C, rfl⟩
      exact ⟨C' * C, Rd.act_mul C' C y⟩
    · rintro ⟨C, hC⟩
      refine ⟨C'⁻¹ * C, ?_⟩
      rw [Rd.act_mul, hC, ← Rd.act_mul, inv_mul_cancel, Rd.act_one]
  have hlift := congrArg
    (Quot.lift (fun w => ∃ C : WeierstrassCurve.VariableChange T, Rd.act C y = w)
      (fun a b hab => propext (key a b hab))) h
  have heq : (∃ C : WeierstrassCurve.VariableChange T, Rd.act C y = y) =
      (∃ C : WeierstrassCurve.VariableChange T, Rd.act C y = z) := hlift
  exact heq.mp ⟨1, Rd.act_one y⟩

end RPBAux

open RPBAux in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A₀ : Type) [CommRing A₀]

    (hℓA : IsUnit ((ℓg : ℕ) : A₀))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsDomain R] [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)

    [DecidableEq (FractionRing R)]
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
        ργ.act (Quot.mk _ y) = Quot.mk _ y') :
    let xR := (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x
    ∃ (hΔ : IsUnit xR.level.2.2.curve.Δ) (V : WeierstrassCurve.VariableChange R) (x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw R),
      (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).act V ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (ι.comp (P₀.classify (ργ.act P₀.univ))) x) = x' ∧
      x'.curve = xR.curve ∧ x'.level.1 = xR.level.1 ∧
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) xR.level.2.2 hΔ ∧

      (ModularCurve.LevelRelabelling.toPoint ((xR.curve).baseChange (FractionRing R))
          (algebraMap R (FractionRing R) x'.level.2.1.xP) (algebraMap R (FractionRing R) x'.level.2.1.yP) =
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
          ModularCurve.LevelRelabelling.toPoint ((xR.curve).baseChange (FractionRing R))
            (algebraMap R (FractionRing R) xR.level.2.1.xP) (algebraMap R (FractionRing R) xR.level.2.1.yP)) ∧
      x'.level.2.1.xQ = x'.level.2.1.xP ∧ x'.level.2.1.yQ = x'.level.2.1.yP := by
  intro xR
  classical

  let Rd := rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯
  let D := Rd.toLevelModuliDatum
  let g : Matrix (Fin 2) (Fin 2) ℤ := ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  let a : ℤ := g 0 0
  let Φ := FractionRing R
  let jR : R →ₐ[A₀] Φ := IsScalarTower.toAlgHom A₀ R Φ
  have hjR : Function.Injective jR := IsFractionRing.injective R Φ
  have hjR' : (jR : R →+* Φ) = algebraMap R Φ := rfl
  have hjR'' : jR.toRingHom = algebraMap R Φ := rfl
  haveI : Fact ℓg.Prime := ⟨hℓg⟩
  have hℓ3 : 3 ≤ ℓg := by omega
  have hℓ2 : ℓg ≠ 2 := by omega

  have hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T)
      (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ := by
    intro T _ _ W C
    obtain ⟨φ, hφ, hV, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W C
    exact ⟨φ, hφ, hV⟩
  have hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ :=
    fun T T' _ _ _ _ f W => WeierstrassProjModel.exists_isCoefficientHom W f.toRingHom
  have hcomm : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
      (P Q : Section W), (𝒢 T W hΔ).mul _ P Q = (𝒢 T W hΔ).mul _ Q P :=
    fun T _ _ W hΔ P Q => GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O hVC hCO T W hΔ P Q

  have hdetZ : g.det = 1 := γ.det_coe
  have hgq : IsUnit ((g.det : ℤ) : ZMod q) := by rw [hdetZ, Int.cast_one]; exact isUnit_one

  have ha : ¬ ((ℓg : ℤ) ∣ a) := by
    intro hdiv
    have h10 : (ℓg : ℤ) ∣ g 1 0 := by
      have h := CongruenceSubgroup.Gamma0_mem.mp hγ
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      exact (Int.natCast_dvd_natCast.mpr hℓgM').trans h
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      have h := hdetZ
      rw [Matrix.det_fin_two] at h
      exact h
    have h1 : (ℓg : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_left hdiv _) (dvd_mul_of_dvd_right h10 _)
    have h2 : (ℓg : ℤ).natAbs ∣ 1 := by simpa using Int.natAbs_dvd_natAbs.mpr h1
    rw [Int.natAbs_natCast, Nat.dvd_one] at h2
    exact hℓg.one_lt.ne' h2

  have hℓR : IsUnit ((ℓg : ℕ) : R) := by simpa using hℓA.map (algebraMap A₀ R)

  obtain ⟨⟨h0, hG1, hDc, hΔ, hB⟩, hLink⟩ := xR.isLevel

  obtain ⟨diam, hd1, hd2, hd3, hd4, hd5, hd6, hd6', hd7⟩ :=
    ModularCurve.LevelRelabelling.exists_natural_zsmul_gamma1Point A₀ ℓg hℓ3 hℓA 𝒢 h𝒢 h𝒢O
  let D' : ModularCurve.LevelPData R := diam R xR.curve a xR.level.2.1
  have hG1' : ModularCurve.IsGamma1Point xR.curve ℓg D' := hd2 R xR.curve xR.isUnit_Δ a ha xR.level.2.1 hG1

  have hLink' : ModularCurve.IsGamma1Link xR.curve ℓg M' xR.level.1 D' := by
    intro hmem
    obtain ⟨S, hS⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
      (xR.curve : WeierstrassCurve.Projective R)).1 _ _).mp hG1.equation_P
    have hS' := hd7 R xR.curve xR.isUnit_Δ a ha xR.level.2.1 hG1 S hS
    obtain ⟨u, -, hue⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection 𝒢 h𝒢 h𝒢O
        ℓg hℓ2 R hℓR (xR.curve : WeierstrassCurve.Projective R) xR.isUnit_Δ S _ _ hS hG1.preΨ_P a ha _ _ hS'
        (ℓg ^ (M'.factorization ℓg - 1))
    rw [hue]
    exact Dvd.dvd.mul_left (hLink hmem) _

  let x' : Rd.Raw R :=
    { curve := xR.curve
      isUnit_Δ := xR.isUnit_Δ
      level := (xR.level.1, D', ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g xR.level.2.2 hΔ)
      isLevel := by
        refine ⟨⟨h0, hG1', hDc, hΔ, ?_⟩, hLink'⟩
        exact IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det (𝒢 R xR.level.2.2.curve hΔ)
          (hcomm R xR.level.2.2.curve hΔ) q xR.level.2.2.P xR.level.2.2.Q hB g hgq }

  have hslot : ∀ (W' : WeierstrassCurve Φ), W' = xR.curve.map jR.toRingHom →
      ModularCurve.LevelRelabelling.toPoint W' (jR D'.xP) (jR D'.yP) =
        a • ModularCurve.LevelRelabelling.toPoint W' (jR xR.level.2.1.xP) (jR xR.level.2.1.yP) := by
    rintro W' rfl
    have hΔΦ' : IsUnit (xR.curve.map jR.toRingHom).Δ := xR.curve.isUnit_Δ_map _ xR.isUnit_Δ
    have hG1Φ : ModularCurve.IsGamma1Point (xR.curve.map jR.toRingHom) ℓg (xR.level.2.1.map jR.toRingHom) :=
      hG1.map jR.toRingHom
    have h1 := hd1 Φ (xR.curve.map jR.toRingHom) hΔΦ' a ha (xR.level.2.1.map jR.toRingHom) hG1Φ
    rw [hd3 R Φ jR xR.curve xR.isUnit_Δ a ha xR.level.2.1 hG1] at h1
    simpa [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP] using h1

  let z : Rd.Raw R := Rd.mapRing (ι.comp (P₀.classify (ργ.act P₀.univ))) x

  have hz : (Quot.mk _ z : D.Pt R) = ργ.act (Quot.mk _ xR) := by
    have e1 : (Quot.mk _ z : D.Pt R) = D.map (ι.comp (P₀.classify (ργ.act P₀.univ))) (Quot.mk _ x) := rfl
    have e2 : (Quot.mk _ xR : D.Pt R) = D.map ι (Quot.mk _ x) := rfl
    rw [e1, e2, D.map_comp, hx, P₀.map_classify, ργ.act_map]

  obtain ⟨⟨-, -, -, hΔΦ, -⟩, -⟩ := (Rd.mapRing jR xR).isLevel
  have hpinΦ : ργ.act (Quot.mk _ (Rd.mapRing jR xR)) = (Quot.mk _ (Rd.mapRing jR x') : D.Pt Φ) := by
    refine hpin Φ (Rd.mapRing jR xR) (Rd.mapRing jR x') hΔΦ rfl rfl ?_ ?_ ?_ ?_
    ·
      exact hslot _ (by simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, Algebra.algebraMap_self]; rfl)
    · exact congrArg jR hG1'.xQ_eq
    · exact congrArg jR hG1'.yQ_eq
    ·
      show 𝒯.map jR (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g xR.level.2.2 hΔ) =
        ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g (𝒯.map jR xR.level.2.2) hΔΦ
      exact LevelTransport.map_relabel_eq_relabel_map 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC hCO R Φ jR g xR.level.2.2 hΔ hΔΦ

  have hmapeq : D.map jR (Quot.mk _ z) = D.map jR (Quot.mk _ x') := by
    rw [hz, ← ργ.act_map]
    exact hpinΦ
  have hcls : (Quot.mk _ z : D.Pt R) = Quot.mk _ x' :=
    map_injective_of_injective D P₀ jR hjR _ _ hmapeq

  obtain ⟨V, hV⟩ := exists_act_eq_of_mk_eq Rd z x' hcls
  refine ⟨hΔ, V, x', hV, rfl, rfl, rfl, ?_, hG1'.xQ_eq, hG1'.yQ_eq⟩

  exact hslot _ rfl

end S_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit (solution)
