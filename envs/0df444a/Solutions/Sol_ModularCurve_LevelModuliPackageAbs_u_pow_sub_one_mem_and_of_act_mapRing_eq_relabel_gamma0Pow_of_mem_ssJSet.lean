-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a589c409-36da-5df1-af15-92d479406ae5

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
import Theorems.Thm_WeierstrassCurve_VariableChange_u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
import Theorems.Thm_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData
import Theorems.Thm_ModularCurve_IsLevelPStructure_map_eq_one_of_relabel_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ"
p2m_attr_erase "simp" "ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

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
    (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)

    (V : WeierstrassCurve.VariableChange R)
    (hΔ : IsUnit ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve.Δ)
    (x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw R)
    (hact : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act V ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (θ₀.restrictScalars A₀) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x)) = x')
    (hcurve : x'.curve = ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).curve)
    (hlev1 : x'.level.1 = ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.1)
    (hlev22 : x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2 hΔ)
    (hlev21 : x'.level.2.1.map (algebraMap R (FractionRing R)) =
      ModularCurve.LevelRelabelling.LevelPData.relabel (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).curve.map (algebraMap R (FractionRing R))) ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
        (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.1.map (algebraMap R (FractionRing R)))) :
    (((V.u : Rˣ) : R) ^ (q + 1) - 1 ∈ maximalIdeal R) ∧
    (γ ∈ CongruenceSubgroup.Gamma ℓ → ((V.u : Rˣ) : R) - 1 ∈ maximalIdeal R) ∧
    (γ ∈ CongruenceSubgroup.Gamma q → γ ∉ CongruenceSubgroup.Gamma ℓ → ((V.u : Rˣ) : R) - 1 ∉ maximalIdeal R) := by
  classical

  let Rd := rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯
  let xR := Rd.mapRing ι x
  let E : WeierstrassCurve R := x.curve.map ι.toRingHom
  let D : ModularCurve.LevelPData R := xR.level.2.1
  let θA : R →ₐ[A₀] R := θ₀.restrictScalars A₀
  let g : Matrix (Fin 2) (Fin 2) ℤ := ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  have hθA : θA.toRingHom = θ₀.toRingHom := rfl
  have hEdef : xR.curve = E := rfl
  have hE : IsUnit E.Δ := by
    have h := xR.isUnit_Δ
    rw [hEdef] at h
    exact h
  have hDlev : ModularCurve.IsLevelPStructure E ℓ D := by
    have h : ModularCurve.IsLevelPStructure xR.curve ℓ D := xR.isLevel.2.1
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
    rw [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map, hresθ] at h
    exact h
  have hEb : IsUnit Eb.Δ := by rw [WeierstrassCurve.map_Δ]; exact hE.map resR
  haveI : Eb.IsElliptic := ⟨hEb⟩
  have hDb : ModularCurve.IsLevelPStructure Eb ℓ Db := hDlev.map resR
  have hVbu : ((Vb.u : kˣ) : k) = resR ((V.u : Rˣ) : R) := by
    simp [Vb, WeierstrassCurve.VariableChange.map]

  have hj₀ : P₀.j₀ = x.curve.jOfUnit x.isUnit_Δ := by
    show Rd.toLevelModuliDatum.jOf P₀.univ = _
    rw [← hx]
    rfl
  have hjE : Eb.j = resR (ι P₀.j₀) := by
    rw [hj₀]
    have e1 : ι.toRingHom (x.curve.jOfUnit x.isUnit_Δ) = E.jOfUnit hE :=
      (x.curve.jOfUnit_map ι.toRingHom x.isUnit_Δ hE).symm
    have e2 : resR (E.jOfUnit hE) = Eb.jOfUnit hEb := (E.jOfUnit_map resR hE hEb).symm
    have e3 : Eb.jOfUnit hEb = Eb.j := Eb.jOfUnit_eq_j hEb
    rw [← e3, ← e2, ← e1]
    rfl

  have h1 : ((V.u : Rˣ) : R) ^ (q + 1) - 1 ∈ maximalIdeal R := by
    let Ω := AlgebraicClosure k
    haveI : CharP Ω q := charP_of_injective_algebraMap (algebraMap k Ω).injective q
    have hss : (algebraMap k Ω) Eb.j ∈ ModularCurve.ssJSet q Ω := by
      rw [hjE]; exact hssJ Ω (algebraMap k Ω)
    have hu := WeierstrassCurve.VariableChange.u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
      q hq k Eb Ω (algebraMap k Ω) hss Vb hVbEb
    rw [hVbu, ← map_pow] at hu
    rw [← hkerR, RingHom.mem_ker, map_sub, map_one, hu, sub_self]

  have hred21 : x'.level.2.1.map resR = Db.variableChange Vb := by
    rw [h21', ModularCurve.LevelPData.map_variableChange, ModularCurve.LevelPData.map_map, hresθ]

  let Fr := FractionRing R
  let jR : R →ₐ[A₀] Fr := IsScalarTower.toAlgHom A₀ R Fr
  have hjR : jR.toRingHom = algebraMap R Fr := rfl
  have hjinj : Function.Injective (algebraMap R Fr) := IsFractionRing.injective R Fr
  have hEF : IsUnit (E.map (algebraMap R Fr)).Δ := by rw [WeierstrassCurve.map_Δ]; exact hE.map _
  have hDF : ModularCurve.IsLevelPStructure (E.map (algebraMap R Fr)) ℓ (D.map (algebraMap R Fr)) := hDlev.map _
  have hgdet : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det := by
    have : (g.map (Int.castRingHom (ZMod ℓ))).det = Int.castRingHom (ZMod ℓ) g.det := (RingHom.map_det _ _).symm
    rw [this, Matrix.SpecialLinearGroup.det_coe, map_one]; exact isUnit_one

  have h2 : γ ∈ CongruenceSubgroup.Gamma ℓ → ((V.u : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro hγℓ
    obtain ⟨-, hone, hmod⟩ :=
      ModularCurve.IsLevelPStructure.relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq
        ℓ hℓ3 (E.map (algebraMap R Fr)) hEF (D.map (algebraMap R Fr)) hDF
    have hg1 : g.map (Int.castRingHom (ZMod ℓ)) = (1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod ℓ)) := by
      rw [map_eq_one_of_mem_Gamma γ hγℓ]; simp [Matrix.map_one]
    have hx21 : x'.level.2.1 = D := by
      apply levelPData_map_injective (algebraMap R Fr) hjinj
      calc x'.level.2.1.map (algebraMap R Fr)
          = ModularCurve.LevelRelabelling.LevelPData.relabel (E.map (algebraMap R Fr)) g (D.map (algebraMap R Fr)) := hlev21
        _ = ModularCurve.LevelRelabelling.LevelPData.relabel (E.map (algebraMap R Fr)) 1 (D.map (algebraMap R Fr)) :=
            hmod g 1 hg1
        _ = D.map (algebraMap R Fr) := hone
    have hfixD : Db.variableChange Vb = Db := by rw [← hred21, hx21]
    have hVb1 : Vb = 1 :=
      ModularCurve.IsLevelPStructure.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
        ℓ hℓ3 (isUnit_iff_ne_zero.mpr hℓk) Eb hEb Db hDb Vb hVbEb hfixD
    have : resR ((V.u : Rˣ) : R) = 1 := by
      rw [← hVbu, hVb1, WeierstrassCurve.VariableChange.one_def]; rfl
    rw [← hkerR, RingHom.mem_ker, map_sub, map_one, this, sub_self]

  have h3 : γ ∈ CongruenceSubgroup.Gamma q → γ ∉ CongruenceSubgroup.Gamma ℓ → ((V.u : Rˣ) : R) - 1 ∉ maximalIdeal R := by
    intro _ hγℓ hu1
    apply hγℓ

    obtain ⟨relab, hrel1, -, hrel3, -, -, -, -⟩ :=
      ModularCurve.LevelRelabelling.exists_natural_relabel_levelPData A₀ ℓ hℓ3 hℓA

    have hFr : x'.level.2.1.map (algebraMap R Fr) = (relab R E g D).map (algebraMap R Fr) := by
      calc x'.level.2.1.map (algebraMap R Fr)
          = ModularCurve.LevelRelabelling.LevelPData.relabel (E.map (algebraMap R Fr)) g (D.map (algebraMap R Fr)) := hlev21
        _ = relab Fr (E.map (algebraMap R Fr)) g (D.map (algebraMap R Fr)) :=
            (hrel1 Fr (E.map (algebraMap R Fr)) hEF g hgdet (D.map (algebraMap R Fr)) hDF).symm
        _ = relab Fr (E.map jR.toRingHom) g (D.map jR.toRingHom) := by rw [hjR]
        _ = (relab R E g D).map jR.toRingHom := hrel3 R Fr jR E hE g hgdet D hDlev
        _ = (relab R E g D).map (algebraMap R Fr) := by rw [hjR]
    have hx21 : x'.level.2.1 = relab R E g D := levelPData_map_injective (algebraMap R Fr) hjinj hFr

    letI : Algebra A₀ k := (resR.comp (algebraMap A₀ R)).toAlgebra
    let resA : R →ₐ[A₀] k := { toRingHom := resR, commutes' := fun a => rfl }
    have hresA : resA.toRingHom = resR := rfl
    have hred : x'.level.2.1.map resR = ModularCurve.LevelRelabelling.LevelPData.relabel Eb g Db := by
      calc x'.level.2.1.map resR
          = (relab R E g D).map resA.toRingHom := by rw [hx21, hresA]
        _ = relab k (E.map resA.toRingHom) g (D.map resA.toRingHom) := (hrel3 R k resA E hE g hgdet D hDlev).symm
        _ = relab k Eb g Db := by rw [hresA]
        _ = ModularCurve.LevelRelabelling.LevelPData.relabel Eb g Db := hrel1 k Eb hEb g hgdet Db hDb

    have hVbu1 : Vb.u = 1 := by
      apply Units.ext
      rw [hVbu, Units.val_one]
      rw [← hkerR, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hu1
      exact hu1
    have hqprime : q.Prime := Fact.out
    have h6 : IsUnit (6 : k) := by
      rw [isUnit_iff_ne_zero, show (6 : k) = ((6 : ℕ) : k) by norm_num, ne_eq, CharP.cast_eq_zero_iff k q]
      intro h
      have h' := (Nat.Prime.dvd_mul hqprime).mp (show q ∣ 2 * 3 by simpa using h)
      rcases h' with h2 | h3
      · have := Nat.le_of_dvd two_pos h2; omega
      · have := Nat.le_of_dvd three_pos h3; omega
    have hVb1 : Vb = 1 :=
      WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six k h6 Eb Vb hVbEb hVbu1
    have hfix : ModularCurve.LevelRelabelling.LevelPData.relabel Eb g Db = Db := by
      rw [← hred, hred21, hVb1, ModularCurve.LevelPData.variableChange_one]
    exact mem_Gamma_of_map_eq_one γ (ModularCurve.IsLevelPStructure.map_eq_one_of_relabel_eq ℓ hℓ3 hℓk Eb hEb Db hDb g hgdet hfix)
  exact ⟨h1, h2, h3⟩

end S_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_u_pow_sub_one_mem_and_of_act_mapRing_eq_relabel_gamma0Pow_of_mem_ssJSet (solution)
