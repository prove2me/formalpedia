-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.exists_isModuliRelabelling_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3cd362c1-9b9b-5da2-aba5-2dafd6e3ae3e

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_relabel_one_mul_of_isUnit_det_gamma0Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_gamma0Pow
p2m_attr_erase "instance" "ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
        IsCoefficientHom W f.toRingHom φ) :
    ∃ ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A T]
        (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
        x'.curve = x.curve →
        x'.level.1 = x.level.1 →
        x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
        x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
        (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∀ (γ γ' : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [CommRing T] [Algebra A T]
        (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ (γ * γ')).act x = (ρ γ').act ((ρ γ).act x)) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ 1).act x = x) ∧
      (∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [CommRing T] [Algebra A T]
        (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
        (ρ γ⁻¹).act ((ρ γ).act x) = x ∧ (ρ γ).act ((ρ γ⁻¹).act x) = x) := by
  classical
  obtain ⟨ρ, hpin, hone, hmul, -⟩ :=
    ModularCurve.LevelRelabelling.exists_problemAut_relabel_one_mul_of_isUnit_det_gamma0Pow q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO

  let Mx : ↥(CongruenceSubgroup.Gamma0 M') → Matrix (Fin 2) (Fin 2) ℤ := fun γ => ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  have hMmul : ∀ γ γ' : ↥(CongruenceSubgroup.Gamma0 M'), Mx (γ * γ') = Mx γ * Mx γ' := by
    intro γ γ'; simp only [Mx, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hMone : Mx 1 = 1 := by simp only [Mx, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
  have hdet : ∀ γ : ↥(CongruenceSubgroup.Gamma0 M'), IsUnit ((Mx γ).map (Int.castRingHom (ZMod (q * ℓ)))).det := by
    intro γ
    have h := (Int.castRingHom (ZMod (q * ℓ))).map_det (Mx γ)
    rw [RingHom.mapMatrix_apply] at h
    rw [← h, Matrix.SpecialLinearGroup.det_coe, map_one]
    exact isUnit_one
  refine ⟨fun γ => ρ (Mx γ), ?_, ?_, ?_, ?_⟩
  ·
    intro γ T _ _ x x' hΔ hc hk hP hD
    exact hpin (Mx γ) (hdet γ) T x x' hΔ hc hk hP hD
  ·
    intro γ γ' T _ _ x
    show (ρ (Mx (γ * γ'))).act x = (ρ (Mx γ')).act ((ρ (Mx γ)).act x)
    rw [hMmul]
    exact hmul (Mx γ) (Mx γ') (hdet γ) (hdet γ') T x
  ·
    intro T _ _ x
    show (ρ (Mx 1)).act x = x
    rw [hMone]; exact hone T x
  ·
    intro γ T _ _ x
    refine ⟨?_, ?_⟩
    · show (ρ (Mx γ⁻¹)).act ((ρ (Mx γ)).act x) = x
      rw [← hmul (Mx γ) (Mx γ⁻¹) (hdet γ) (hdet γ⁻¹) T x, ← hMmul, mul_inv_cancel, hMone]
      exact hone T x
    · show (ρ (Mx γ)).act ((ρ (Mx γ⁻¹)).act x) = x
      rw [← hmul (Mx γ⁻¹) (Mx γ) (hdet γ⁻¹) (hdet γ) T x, ← hMmul, inv_mul_cancel, hMone]
      exact hone T x

end S_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_exists_isModuliRelabelling_gamma0Pow (solution)
