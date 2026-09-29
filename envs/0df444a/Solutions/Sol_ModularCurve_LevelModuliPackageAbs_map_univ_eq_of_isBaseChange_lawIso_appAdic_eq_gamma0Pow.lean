-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b19b1a99-b433-52c3-9c65-f327caa67318

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
import Definitions.Def_WeierstrassCurve_FormalGroup
import Mathlib
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_map_eq_one_smul_map_eq_map_of_lawIso_gamma0Pow
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_levelPData_map_eq_variableChange_of_smul_map_eq_gamma0Pow
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_gamma0Pow
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃"

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

namespace GlueCoreHelper

variable (q ℓ M' : ℕ) (A₀ : Type) [CommRing A₀]
  (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
      ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
  (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
      ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
  (𝒢 : GroupLaws A₀) (𝒯 : LevelTransport A₀ 𝒢 q)

theorem quotMk_eq_quotMk_iff (T : Type) [CommRing T] [Algebra A₀ T]
    (x y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T) = Quot.mk _ y ↔
      ∃ C : WeierstrassCurve.VariableChange T, y = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C x := by
  have hsymm : ∀ {a b : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T},
      (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Rel a b → (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Rel b a := by
    rintro a b ⟨C, rfl⟩
    exact ⟨C⁻¹, by rw [← (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act_mul, inv_mul_cancel, (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act_one]⟩
  have hequiv : Equivalence ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Rel (T := T)) :=
    ⟨fun a => ModularCurve.RigidWeierstrassData.Rel.refl _ a, fun h => hsymm h,
      fun h h' => ModularCurve.RigidWeierstrassData.Rel.trans _ h h'⟩
  constructor
  · intro h
    exact (hequiv.eqvGen_iff).mp (Quot.eqvGen_exact h)
  · intro h; exact Quot.sound h

theorem map_univ_eq
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (T : Type) [CommRing T] [Algebra A₀ T] (φ : P₀.B₀ →ₐ[A₀] T) :
    (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ =
      Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing φ x) := by
  rw [← hx]; rfl

theorem existsUnique_algHom_rel_mapRing
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (T : Type) [CommRing T] [Algebra A₀ T] (y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    ∃! φ : P₀.B₀ →ₐ[A₀] T,
      ∃ C : WeierstrassCurve.VariableChange T, y = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing φ x) := by
  have key : ∀ φ : P₀.B₀ →ₐ[A₀] T,
      (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ = Quot.mk _ y ↔
        ∃ C : WeierstrassCurve.VariableChange T, y = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C
          ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing φ x) := by
    intro φ
    rw [map_univ_eq q ℓ M' A₀ hℓ hM 𝒢 𝒯 P₀ x hx T φ]
    exact quotMk_eq_quotMk_iff q ℓ M' A₀ hℓ hM 𝒢 𝒯 T _ y
  obtain ⟨φ, hφ, huniq⟩ := P₀.represents T (Quot.mk _ y)
  exact ⟨φ, (key φ).mp hφ, fun φ' h' => huniq φ' ((key φ').mpr h')⟩

end GlueCoreHelper

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
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
    (χP χQ : OriginChartRing (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve) →+* R)
    (hP : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
    (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (hT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (y₀ y₁ : T) (hy₀ : y₀ ∈ maximalIdeal T) (hy₁ : y₁ ∈ maximalIdeal T)
    (hDy : G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁)
    (φ₁ φ₂ : R →ₐ[W₀] T)
    (h₁ : (∀ r : R, resT (φ₁ r) = resR r) ∧
        ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₁.toRingHom F') (ψ : FormalGroup.LawIso F' G),
          (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₁ (originParam χP)) = y₀ ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₁ (originParam χQ)) = y₁)
    (h₂ : (∀ r : R, resT (φ₂ r) = resR r) ∧
        ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₂.toRingHom F') (ψ : FormalGroup.LawIso F' G),
          (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χP)) = y₀ ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χQ)) = y₁) :
    (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((φ₁.restrictScalars A₀).comp ι) P₀.univ =
      (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((φ₂.restrictScalars A₀).comp ι) P₀.univ :=by
  obtain ⟨C, hC, hCE⟩ := ModularCurve.LevelModuliPackageAbs.exists_variableChange_map_eq_one_smul_map_eq_map_of_lawIso_gamma0Pow q hq2 ℓ M' hℓ3 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ χP χQ hP hQ hD T resT hsT hkT hT₀ G hG y₀ y₁ hy₀ hy₁ hDy φ₁ φ₂ h₁ h₂
  have h2 := ModularCurve.LevelModuliPackageAbs.levelPData_map_eq_variableChange_of_smul_map_eq_gamma0Pow q hq2 ℓ M' hℓ3 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ χP χQ hP hQ hD T resT hsT hkT hT₀ G hG y₀ y₁ hy₀ hy₁ hDy φ₁ φ₂ h₁ h₂ C hC hCE
  have h3 := ModularCurve.LevelModuliPackageAbs.kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_gamma0Pow q hq2 ℓ M' hℓ3 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ χP χQ hP hQ hD T resT hsT hkT hT₀ G hG y₀ y₁ hy₀ hy₁ hDy φ₁ φ₂ h₁ h₂ C hC hCE
  have h4 := ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow q hq2 ℓ M' hℓ3 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ χP χQ hP hQ hD T resT hsT hkT hT₀ G hG y₀ y₁ hy₀ hy₁ hDy φ₁ φ₂ h₁ h₂ C hC hCE
  rw [GlueCoreHelper.map_univ_eq q ℓ M' A₀ hℓ hM 𝒢 𝒯 P₀ x hx T ((φ₁.restrictScalars A₀).comp ι),
    GlueCoreHelper.map_univ_eq q ℓ M' A₀ hℓ hM 𝒢 𝒯 P₀ x hx T ((φ₂.restrictScalars A₀).comp ι)]
  exact (GlueCoreHelper.quotMk_eq_quotMk_iff q ℓ M' A₀ hℓ hM 𝒢 𝒯 T _ _).mpr
    ⟨C, ModularCurve.LevelComponent.Raw.ext' hCE.symm (Prod.ext (funext h3) (Prod.ext h2 h4))⟩

end S_ModularCurve_LevelModuliPackageAbs_map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow (solution)
