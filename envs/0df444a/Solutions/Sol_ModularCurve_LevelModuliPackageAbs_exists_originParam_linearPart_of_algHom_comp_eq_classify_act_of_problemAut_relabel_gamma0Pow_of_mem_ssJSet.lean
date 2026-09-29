-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/806f7ec1-037f-507a-a1bb-638673e2858f

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
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_of_isDomain_gamma0Pow_of_isUnit
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_apply_originParam_sub_inv_u_mul_mem_sq_of_act_mapRing_eq_relabel_gamma0Pow
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet
p2m_attr_erase "instance" "ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing"
p2m_attr_erase "instance" "WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsCommFormalGroup"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq : 5 ≤ q) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hℓA : IsUnit ((ℓ : ℕ) : A₀))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

    [IsDomain R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
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
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)

    (hssJ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ιΩ : k →+* Ω),
      ιΩ (resR (ι P₀.j₀)) ∈ ModularCurve.ssJSet q Ω)

    (χP χQ : OriginChartRing ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R)
    (hP : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
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
    (ργ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [Algebra A₀ T]
        (y y' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y')
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R)

    (θ₀ : R →ₐ[W₀] R)
    (hcompl : ∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b))
    (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R) :
    ∃ c : R,

      (θ₀ (originParam χP) - c * (((γ 0 0 : ℤ) : R) * originParam χP + ((γ 1 0 : ℤ) : R) * originParam χQ) ∈ (maximalIdeal R) ^ 2) ∧
      (θ₀ (originParam χQ) - c * (((γ 0 1 : ℤ) : R) * originParam χP + ((γ 1 1 : ℤ) : R) * originParam χQ) ∈ (maximalIdeal R) ^ 2) ∧
      (c ^ (q + 1) - 1 ∈ maximalIdeal R) ∧
      (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ maximalIdeal R) ∧
      (γ ∈ CongruenceSubgroup.Gamma q → γ ∉ CongruenceSubgroup.Gamma ℓ → c - 1 ∉ maximalIdeal R) := by
  classical
  have hcomp : (θ₀.restrictScalars A₀).comp ι = ι.comp (P₀.classify (ργ.act P₀.univ)) := by
    apply AlgHom.ext; intro b; exact hcompl b
  obtain ⟨hΔ, V, x', hact, hcurve, hlev1, hlev22, hlev21⟩ :=
    ModularCurve.LevelModuliPackageAbs.exists_variableChange_act_mapRing_classify_act_univ_eq_relabel_of_isDomain_gamma0Pow_of_isUnit
      q ℓ M' hℓ3 A₀ hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι γ ργ hpin
  rw [← hcomp, (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_comp] at hact
  obtain ⟨hl0, hl1⟩ :=
    ModularCurve.LevelModuliPackageAbs.apply_originParam_sub_inv_u_mul_mem_sq_of_act_mapRing_eq_relabel_gamma0Pow
      q hq2 hq ℓ M' hℓ3 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hℓA hVC hCO P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ hssJ χP χQ hP hQ hBC hDr hmax huniv γ hγ ργ hpin hfix θ₀ hcompl hres V hΔ x' hact hcurve hlev1 hlev22 hlev21
  obtain ⟨hs1, hs2, hs3⟩ :=
    ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet
      q hq2 hq ℓ M' hℓ3 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hℓA hVC hCO P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ hssJ χP χQ hP hQ hBC hDr hmax huniv γ hγ ργ hpin hfix θ₀ hcompl hres V hΔ x' hact hcurve hlev1 hlev22 hlev21
  have key : ((V.u⁻¹ : Rˣ) : R) * ((V.u : Rˣ) : R) = 1 := Units.inv_mul _
  have keyn : ((V.u⁻¹ : Rˣ) : R) ^ (q + 1) * ((V.u : Rˣ) : R) ^ (q + 1) = 1 := by rw [← mul_pow, key, one_pow]
  refine ⟨((V.u⁻¹ : Rˣ) : R), hl0, hl1, ?_, ?_, ?_⟩
  · have e : ((V.u⁻¹ : Rˣ) : R) ^ (q + 1) - 1 = -(((V.u⁻¹ : Rˣ) : R) ^ (q + 1)) * (((V.u : Rˣ) : R) ^ (q + 1) - 1) := by
      linear_combination keyn
    rw [e]; exact Ideal.mul_mem_left _ _ hs1
  · intro hγℓ
    have e : ((V.u⁻¹ : Rˣ) : R) - 1 = -((V.u⁻¹ : Rˣ) : R) * (((V.u : Rˣ) : R) - 1) := by linear_combination key
    rw [e]; exact Ideal.mul_mem_left _ _ (hs2 hγℓ)
  · intro hγq hγℓ hmem
    apply hs3 hγq hγℓ
    have e : ((V.u : Rˣ) : R) - 1 = -((V.u : Rˣ) : R) * (((V.u⁻¹ : Rˣ) : R) - 1) := by linear_combination key
    rw [e]; exact Ideal.mul_mem_left _ _ hmem

end S_ModularCurve_LevelModuliPackageAbs_exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_originParam_linearPart_of_algHom_comp_eq_classify_act_of_problemAut_relabel_gamma0Pow_of_mem_ssJSet (solution)
