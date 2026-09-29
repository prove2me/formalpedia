-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5ad8a2e4-41e9-57e9-9ffa-b2e182b0a642

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

import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_rigidDataH1Pow
import Theorems.Thm_IsAdicComplete_existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing"
p2m_attr_erase "instance" "ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv"
p2m_attr_erase "simp" "ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] SubalgebraClass.toAlgebra
attribute [local instance 10001] AdicCompletion.instAlgebra

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

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
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R) :
    ∃ θ₀ : R ≃ₐ[W₀] R,

      (∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b)) ∧

      (∀ r : R, θ₀ r - r ∈ maximalIdeal R) := by
  classical
  have hℓg3 : 3 ≤ ℓg := by omega

  let Rd := rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯
  let D := Rd.toLevelModuliDatum
  let a : P₀.B₀ →ₐ[A₀] P₀.B₀ := P₀.classify (ργ.act P₀.univ)

  obtain ⟨ρ', hρ'pin, -, -, hρ'inv⟩ :=
    ModularCurve.LevelRelabelling.exists_isModuliRelabelling_rigidDataH1Pow q M' ℓg hℓg hℓg3 hℓgM' A₀ hℓA hℓ hM hL 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO
  let γ₀ : ↥(CongruenceSubgroup.Gamma0 M') := ⟨γ, hγ⟩
  let σ := ρ' γ₀
  let σ' := ρ' γ₀⁻¹
  let aσ : P₀.B₀ →ₐ[A₀] P₀.B₀ := P₀.classify (σ.act P₀.univ)
  let aσ' : P₀.B₀ →ₐ[A₀] P₀.B₀ := P₀.classify (σ'.act P₀.univ)
  have hσpin : ∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
      (y y' : Rd.Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
      y'.curve = y.curve →
      y'.level.1 = y.level.1 →
      ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y'.level.2.1.xP y'.level.2.1.yP =
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
          ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y.level.2.1.xP y.level.2.1.yP →
      y'.level.2.1.xQ = y'.level.2.1.xP → y'.level.2.1.yQ = y'.level.2.1.yP →
      y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
      σ.act (Quot.mk _ y) = Quot.mk _ y' :=
    fun T _ _ _ y y' hΔ h1 h2 h3 h4 h5 h6 => hρ'pin γ₀ T y y' hΔ h1 h2 h3 h4 h5 h6

  have step1 : ι.comp a = ι.comp aσ := by
    obtain ⟨hΔ₁, V₁, x₁, hact₁, hc₁, hl₁, h22₁, hP₁, hxQ₁, hyQ₁⟩ :=
      ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
        q M' ℓg hℓg hℓg12 hℓgM' A₀ hℓA hℓ hM hL 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι γ hγ ργ hpin
    obtain ⟨hΔ₂, V₂, x₂, hact₂, hc₂, hl₂, h22₂, hP₂, hxQ₂, hyQ₂⟩ :=
      ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_toPoint_of_mem_gamma0_of_isDomain_rigidDataH1Pow_of_isUnit
        q M' ℓg hℓg hℓg12 hℓgM' A₀ hℓA hℓ hM hL 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι γ hγ σ hσpin

    have h21 : x₁.level.2.1 = x₂.level.2.1 := by
      have hj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)

      have hΔ0 : ((Rd.mapRing ι x).curve.baseChange (FractionRing R)).Δ ≠ 0 := by
        rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
        exact fun h0 => (Rd.mapRing ι x).isUnit_Δ.ne_zero (hj (by rw [h0, map_zero]))
      have hns : ∀ (y : Rd.Raw R), y.curve = (Rd.mapRing ι x).curve →
          ((Rd.mapRing ι x).curve.baseChange (FractionRing R)).toAffine.Nonsingular
            (algebraMap R (FractionRing R) y.level.2.1.xP) (algebraMap R (FractionRing R) y.level.2.1.yP) := by
        intro y hy
        have hG : ModularCurve.IsGamma1Point y.curve ℓg y.level.2.1 := y.isLevel.1.2.1
        have heq : ((Rd.mapRing ι x).curve.baseChange (FractionRing R)).toAffine.Equation
            (algebraMap R (FractionRing R) y.level.2.1.xP) (algebraMap R (FractionRing R) y.level.2.1.yP) := by
          rw [← hy]
          exact (WeierstrassCurve.Affine.Equation.map (algebraMap R (FractionRing R)) hG.equation_P)
        exact (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ0).mp heq
      have hsome : ∀ (y : Rd.Raw R) (hy : y.curve = (Rd.mapRing ι x).curve),
          ModularCurve.LevelRelabelling.toPoint ((Rd.mapRing ι x).curve.baseChange (FractionRing R))
            (algebraMap R (FractionRing R) y.level.2.1.xP) (algebraMap R (FractionRing R) y.level.2.1.yP) =
          WeierstrassCurve.Affine.Point.some _ _ (hns y hy) := by
        intro y hy
        unfold ModularCurve.LevelRelabelling.toPoint
        rw [dif_pos (hns y hy)]
      have e := hP₁.trans hP₂.symm
      rw [hsome x₁ hc₁, hsome x₂ hc₂, WeierstrassCurve.Affine.Point.some.injEq] at e
      have hxP : x₁.level.2.1.xP = x₂.level.2.1.xP := hj e.1
      have hyP : x₁.level.2.1.yP = x₂.level.2.1.yP := hj e.2
      apply ModularCurve.LevelPData.ext
      · exact hxP
      · exact hyP
      · rw [hxQ₁, hxQ₂, hxP]
      · rw [hyQ₁, hyQ₂, hyP]
    have h22 : x₁.level.2.2 = x₂.level.2.2 := by rw [h22₁, h22₂]
    have hx12 : x₁ = x₂ :=
      ModularCurve.LevelComponent.Raw.ext' (hc₁.trans hc₂.symm)
        (Prod.ext (hl₁.trans hl₂.symm) (Prod.ext h21 h22))

    have hpt : (Quot.mk _ (Rd.mapRing (ι.comp a) x) : Rd.Pt R) = Quot.mk _ (Rd.mapRing (ι.comp aσ) x) := by
      calc (Quot.mk _ (Rd.mapRing (ι.comp a) x) : Rd.Pt R)
          = Quot.mk _ (Rd.act V₁ (Rd.mapRing (ι.comp a) x)) := Quot.sound ⟨V₁, rfl⟩
        _ = Quot.mk _ x₁ := by rw [hact₁]
        _ = Quot.mk _ x₂ := by rw [hx12]
        _ = Quot.mk _ (Rd.act V₂ (Rd.mapRing (ι.comp aσ) x)) := by rw [hact₂]
        _ = Quot.mk _ (Rd.mapRing (ι.comp aσ) x) := (Quot.sound ⟨V₂, rfl⟩).symm
    have hmap : D.map (ι.comp a) P₀.univ = D.map (ι.comp aσ) P₀.univ := by
      rw [← hx]
      show Rd.map (ι.comp a) (Quot.mk _ x) = Rd.map (ι.comp aσ) (Quot.mk _ x)
      rw [ModularCurve.RigidWeierstrassData.map_mk, ModularCurve.RigidWeierstrassData.map_mk]
      exact hpt
    exact (P₀.classify_unique _ (ι.comp a) hmap).trans (P₀.classify_unique _ (ι.comp aσ) rfl).symm
  have step1' : ∀ b : P₀.B₀, ι (a b) = ι (aσ b) := fun b => by
    have := congrArg (fun f : P₀.B₀ →ₐ[A₀] R => f b) step1
    simpa using this

  have hid : D.map (AlgHom.id A₀ P₀.B₀) P₀.univ = P₀.univ := D.map_id _ _
  have inv1 : aσ.comp aσ' = AlgHom.id A₀ P₀.B₀ := by
    have h : D.map (aσ.comp aσ') P₀.univ = P₀.univ := by
      rw [D.map_comp, P₀.map_classify, ← σ'.act_map, P₀.map_classify]
      exact (hρ'inv γ₀ P₀.B₀ P₀.univ).1
    exact (P₀.classify_unique _ _ h).trans (P₀.classify_unique _ _ hid).symm
  have inv2 : aσ'.comp aσ = AlgHom.id A₀ P₀.B₀ := by
    have h : D.map (aσ'.comp aσ) P₀.univ = P₀.univ := by
      rw [D.map_comp, P₀.map_classify, ← σ.act_map, P₀.map_classify]
      exact (hρ'inv γ₀ P₀.B₀ P₀.univ).2
    exact (P₀.classify_unique _ _ h).trans (P₀.classify_unique _ _ hid).symm
  have inv1' : ∀ b : P₀.B₀, aσ (aσ' b) = b := fun b => by
    have := congrArg (fun f : P₀.B₀ →ₐ[A₀] P₀.B₀ => f b) inv1
    simpa using this
  have inv2' : ∀ b : P₀.B₀, aσ' (aσ b) = b := fun b => by
    have := congrArg (fun f : P₀.B₀ →ₐ[A₀] P₀.B₀ => f b) inv2
    simpa using this

  have hres_a : ∀ b : P₀.B₀, resR ((ι.comp a) b) = resR (ι b) := fun b => by
    have h := hfix b
    rw [← hkerR, RingHom.mem_ker, map_sub, sub_eq_zero] at h
    simpa using h
  have hres_aσ' : ∀ b : P₀.B₀, resR ((ι.comp aσ') b) = resR (ι b) := fun b => by
    have h := hres_a (aσ' b)
    simp only [AlgHom.comp_apply] at h ⊢
    rw [step1' (aσ' b), inv1'] at h
    exact h.symm
  obtain ⟨Φ, ⟨hΦres, hΦι⟩, -⟩ :=
    IsAdicComplete.existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
      A₀ P₀.B₀ R ι k resR hresR hkerR W₀ res₀ hresR₀ hfac (ι.comp a) hres_a
  obtain ⟨Ψ, ⟨hΨres, hΨι⟩, -⟩ :=
    IsAdicComplete.existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
      A₀ P₀.B₀ R ι k resR hresR hkerR W₀ res₀ hresR₀ hfac (ι.comp aσ') hres_aσ'

  have huniq := IsAdicComplete.existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
      A₀ P₀.B₀ R ι k resR hresR hkerR W₀ res₀ hresR₀ hfac ι (fun _ => rfl)
  have hid_ok : (∀ r : R, resR ((AlgHom.id W₀ R) r) = resR r) ∧ ∀ b : P₀.B₀, (AlgHom.id W₀ R) (ι b) = ι b :=
    ⟨fun _ => rfl, fun _ => rfl⟩
  have hΨΦ : Ψ.comp Φ = AlgHom.id W₀ R := by
    apply huniq.unique _ hid_ok
    refine ⟨fun r => ?_, fun b => ?_⟩
    · rw [AlgHom.comp_apply, hΨres, hΦres]
    · rw [AlgHom.comp_apply, hΦι, AlgHom.comp_apply, step1' b]
      have := hΨι (aσ b)
      rw [AlgHom.comp_apply, inv2'] at this
      exact this
  have hΦΨ : Φ.comp Ψ = AlgHom.id W₀ R := by
    apply huniq.unique _ hid_ok
    refine ⟨fun r => ?_, fun b => ?_⟩
    · rw [AlgHom.comp_apply, hΦres, hΨres]
    · rw [AlgHom.comp_apply, hΨι, AlgHom.comp_apply]
      have := hΦι (aσ' b)
      rw [AlgHom.comp_apply, step1' (aσ' b), inv1'] at this
      exact this

  refine ⟨AlgEquiv.ofAlgHom Φ Ψ hΦΨ hΨΦ, fun b => ?_, fun r => ?_⟩
  · show Φ (ι b) = ι (a b)
    have := hΦι b
    simpa using this
  · show Φ r - r ∈ maximalIdeal R
    rw [← hkerR, RingHom.mem_ker, map_sub, hΦres, sub_self]

end S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_comp_eq_classify_act_of_problemAut_relabel_of_factorsThrough_rigidDataH1Pow (solution)
