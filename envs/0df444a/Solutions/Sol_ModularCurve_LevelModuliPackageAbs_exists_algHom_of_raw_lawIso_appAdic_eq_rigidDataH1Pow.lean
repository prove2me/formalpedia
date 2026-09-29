-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/223963ab-fd3c-5d45-9933-d32584c1cdfa

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
import Definitions.Def_WeierstrassCurve_FormalGroup
import Mathlib
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_rigidDataH1Pow
import Theorems.Thm_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_rigidDataH1Pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_IsAdicComplete_of_isNilpotent
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algHom_of_raw_lawIso_appAdic_eq_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

namespace GCGlue

theorem aux_bc_originParam {R T : Type} [CommRing R] [CommRing T] (WR : WeierstrassCurve R) (f : R →+* T)
    (W₁ : WeierstrassCurve T) (h : W₁ = WR.map f)
    (P : Section WR) (χ : OriginChartRing WR →+* R) (I : Ideal R) (hP : ReducesToOrigin P χ I)
    (P₁ : Section W₁)
    (hP₁ : ∀ (φ : projModelGradingCR WR →+*ᵍ projModelGradingCR (WR.map f))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (WR.map f)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR WR)).map φ),
        IsCoefficientHom WR f φ →
          P₁.1 ≫ eqToHom (congrArg projModelCR h) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f) ≫ P.1) :
    ∃ χ₁ : OriginChartRing W₁ →+* T, ReducesToOrigin P₁ χ₁ (I.map f) ∧ originParam χ₁ = f (originParam χ) := by
  subst h
  obtain ⟨φ, hφ, hco⟩ := WeierstrassProjModel.exists_isCoefficientHom WR f
  have h1 := hP₁ φ hφ hco
  rw [eqToHom_refl, Category.id_comp] at h1
  obtain ⟨χ₁, h2, h3, -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
      WR f φ hφ hco P χ I hP P₁ h1
  exact ⟨χ₁, h2, h3⟩

theorem reducesToOrigin_mono {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T} (P : Section W)
    (χ : OriginChartRing W →+* T) {I J : Ideal T} (hIJ : I ≤ J) (h : ReducesToOrigin P χ I) :
    ReducesToOrigin P χ J :=
  ⟨h.1, hIJ h.2.1, hIJ h.2.2⟩

theorem rel_of_eqvGen {A : Type} [CommRing A] (Rg : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] {a b : Rg.Raw T} (h : Relation.EqvGen (Rg.Rel (T := T)) a b) :
    Rg.Rel a b := by
  induction h with
  | rel _ _ h => exact h
  | refl a => exact ModularCurve.RigidWeierstrassData.Rel.refl Rg a
  | symm a b _ ih =>
    obtain ⟨C, rfl⟩ := ih
    exact ⟨C⁻¹, by rw [← Rg.act_mul, inv_mul_cancel, Rg.act_one]⟩
  | trans a b c _ _ ih₁ ih₂ => exact ModularCurve.RigidWeierstrassData.Rel.trans Rg ih₁ ih₂

end GCGlue

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M'] (hℓgM' : ℓg ∣ M')
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
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
    (χP χQ : OriginChartRing (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve) →+* R)
    (hP : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
    (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (hT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (y₀ y₁ : T) (hy₀ : y₀ ∈ maximalIdeal T) (hy₁ : y₁ ∈ maximalIdeal T)
    (hDy : G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁)
    (hpt : ∃ (yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T)
      (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
      (GT : FormalGroup T) (_ : GT.toPowerSeries = yT.level.2.2.curve.formalGroupLawFixed)
      (ψ : FormalGroup.LawIso GT G),
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
      ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T) ∧ ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T) ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χPT) = y₀ ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQT) = y₁ ∧

      yT.curve.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR ∧
      yT.level.2.1.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1).map resR ∧
      (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1 pf).map resR)) :
    ∃ φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
        ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
          (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁ := by
  classical
  obtain ⟨yT, χPT, χQT, GT, hGT, ψ, hψ, hPT, hQT, hψP, hψQ, hcurve, hlev, hker⟩ := hpt

  have hres := ModularCurve.LevelModuliPackageAbs.residue_classify_eq_of_map_residue_eq_rigidDataH1Pow
    q ℓg M' hℓg hℓg12 hℓgM' A₀ hℓ hM hL 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 P₀ x hx R ι k hℓk hM'k resR hresR hkerR W₀ hW₀ res₀ hres₀ hker₀ hresR₀ hfac F hFW F₀ hF₀W hF₀ χP χQ hP hQ hD T resT hsT hkT hT₀ yT χPT χQT hPT hQT hcurve hlev hker

  obtain ⟨Φ, ⟨hΦres, hΦι⟩, -⟩ :=
    hfac T resT hsT hkT hT₀ (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T)) hres

  have hmap : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T)) P₀.univ =
      (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T) := P₀.map_classify _
  rw [← hx] at hmap
  have hmap' : (Quot.mk _ ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T)) x) : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T) =
      Quot.mk _ yT := hmap
  obtain ⟨C, hC⟩ := GCGlue.rel_of_eqvGen _ (Quot.eqvGen_exact hmap')

  generalize hφ₀ : P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T) = φ₀ at hres hΦι hC

  have hresRing : resT.comp φ₀.toRingHom = resR.comp ι.toRingHom := RingHom.ext hres
  have hxRcurve : (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve :=
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).isLevel.1.2.2.1
  have hcurve' : yT.curve.map resT = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).curve.map resT := by
    rw [hcurve, hxRcurve]
    show ((x.curve.map ι.toRingHom).map resR) = (x.curve.map φ₀.toRingHom).map resT
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hresRing]
  have hlev' : yT.level.2.1.map resT = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.1.map resT := by
    rw [hlev]
    show (x.level.2.1.map ι.toRingHom).map resR = (x.level.2.1.map φ₀.toRingHom).map resT
    rw [ModularCurve.LevelPData.map_map, ModularCurve.LevelPData.map_map, hresRing]
  have hC1 : C.map resT = 1 :=
    ModularCurve.FullLevel.variableChange_map_eq_one_of_eq_act_of_map_residue_eq_rigidDataH1Pow q ℓg M' hℓg hℓg12 A₀ hℓ hM hL 𝒢 𝒯 T k resT hℓk
      ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x) yT C hC hcurve' hlev'
  subst hC

  haveI : IsAdicComplete (maximalIdeal T) T :=
    IsAdicComplete.of_isNilpotent
      ((IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal T) bot_ne_top) ▸ IsArtinianRing.isNilpotent_jacobson_bot)
  have hΦ'ι : (Φ.restrictScalars A₀).comp ι = φ₀ := AlgHom.ext hΦι
  have hzz : 𝒯.map (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2 := by
    show 𝒯.map (Φ.restrictScalars A₀) (𝒯.map ι x.level.2.2) = 𝒯.map φ₀ x.level.2.2
    rw [← 𝒯.map_comp, hΦ'ι]

  obtain ⟨hc₂, hpin₂⟩ := h𝒯.2 R T (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2
  have hmI : (maximalIdeal R).map (Φ.restrictScalars A₀).toRingHom ≤ maximalIdeal T := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [← hkerR, RingHom.mem_ker] at hr
    rw [Ideal.mem_comap, ← hkT, RingHom.mem_ker]
    show resT (Φ r) = 0
    rw [hΦres, hr]
  have hχ : ∀ (S : Section ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve)
      (χ : OriginChartRing ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R), ReducesToOrigin S χ (maximalIdeal R) →
      ∀ S₁ : Section (𝒯.map (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve,
        (∀ (φ : projModelGradingCR ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+*ᵍ
            projModelGradingCR (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.map (Φ.restrictScalars A₀).toRingHom))
          (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR
              (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.map (Φ.restrictScalars A₀).toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve)).map φ),
          IsCoefficientHom ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve (Φ.restrictScalars A₀).toRingHom φ →
            S₁.1 ≫ eqToHom (congrArg projModelCR hc₂) ≫ Proj.map φ hφ =
              Spec.map (CommRingCat.ofHom (Φ.restrictScalars A₀).toRingHom) ≫ S.1) →
        ∃ χ₁ : OriginChartRing (𝒯.map (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve →+* T,
          ReducesToOrigin S₁ χ₁ (maximalIdeal T) ∧ originParam χ₁ = Φ (originParam χ) := by
    intro S χ hS S₁ hS₁
    obtain ⟨χ₁, h1, h2⟩ := GCGlue.aux_bc_originParam _ (Φ.restrictScalars A₀).toRingHom _ hc₂ S χ _ hS S₁ hS₁
    exact ⟨χ₁, GCGlue.reducesToOrigin_mono _ _ hmI h1, h2⟩
  obtain ⟨χP₁, hP₁, hzP⟩ := hχ _ χP hP _ (fun φ hφ hco => (hpin₂ φ hφ hco).1)
  obtain ⟨χQ₁, hQ₁, hzQ⟩ := hχ _ χQ hQ _ (fun φ hφ hco => (hpin₂ φ hφ hco).2)
  have hPQ : ∃ (χP₂ χQ₂ : OriginChartRing (𝒯.map (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve →+* T),
      ReducesToOrigin (𝒯.map (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).P χP₂ (maximalIdeal T) ∧
        originParam χP₂ = Φ (originParam χP) ∧
      ReducesToOrigin (𝒯.map (Φ.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).Q χQ₂ (maximalIdeal T) ∧
        originParam χQ₂ = Φ (originParam χQ) :=
    ⟨χP₁, χQ₁, hP₁, hzP, hQ₁, hzQ⟩
  rw [hzz] at hPQ
  obtain ⟨χP₂, χQ₂, hP₂, hzP₂, hQ₂, hzQ₂⟩ := hPQ

  obtain ⟨hc₁, hpin₁⟩ := h𝒯.1 T C ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2
  obtain ⟨φv, hφv, hvc, -, -⟩ :=
    WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2.curve C
  have hPP' := (hpin₁ φv hφv hvc).1
  have hQQ' := (hpin₁ φv hφv hvc).2

  have hbc : F.IsBaseChange Φ.toRingHom (F.map Φ.toRingHom) := rfl
  have hF' : (F.map Φ.toRingHom).toPowerSeries = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2.curve.formalGroupLawFixed := by
    show MvPowerSeries.map Φ.toRingHom F.toPowerSeries = _
    rw [hFW, ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ Φ.toRingHom).2, ← hzz, hc₂]
    rfl

  obtain ⟨ψ', hψ'1, hψ'P, hψ'Q⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
      resT hsT hkT ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2.curve C hC1 _ hc₁ φv hφv hvc
      ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2.P ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing φ₀ x).level.2.2.Q χP₂ χQ₂ hP₂ hQ₂
      _ _ χPT χQT hPT hQT hPP' hQQ' (F.map Φ.toRingHom) hF' GT hGT G ψ hψ y₀ y₁ hψP hψQ
  refine ⟨Φ, hΦres, F.map Φ.toRingHom, hbc, ψ', hψ'1, ?_, ?_⟩
  · rw [← hzP₂]; exact hψ'P
  · rw [← hzQ₂]; exact hψ'Q

end S_ModularCurve_LevelModuliPackageAbs_exists_algHom_of_raw_lawIso_appAdic_eq_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algHom_of_raw_lawIso_appAdic_eq_rigidDataH1Pow (solution)
