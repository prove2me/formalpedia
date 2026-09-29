-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cfce879e-27fc-5855-8335-557051b09e6c

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
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
import Theorems.Thm_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_exists_lawHom_series_eq_variableChangeSeries
import Theorems.Thm_WeierstrassCurve_variableChangeSeries_one
import Theorems.Thm_FormalGroup_LawHom_appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false
universe u
p2m_open "ModularCurve P2MW.S_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow.ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup"
attribute [local instance] MvPolynomial.gradedAlgebra

p2m_open "ModularCurve P2MW.S_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow.ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup"

open CategoryTheory AlgebraicGeometry

namespace ModularCurve
p2m_export "ModularCurve" "LevelModuliPackageAbs kernelVariableChangeDeg LevelPData gamma0PowDeg IsGamma0PowAt IsGamma1Point inLineMulPoly"
namespace LevelModuliPackageAbs
p2m_export "ModularCurve.LevelModuliPackageAbs" "B₀ mk univ represents"
namespace DrinPairEq
p2m_open "ModularCurve.LevelModuliPackageAbs ModularCurve"

open WeierstrassCurve.DrinfeldGlobal

theorem rawDrinfeldPair_ext {T : Type u} [CommRing T] :
    ∀ (x y : RawDrinfeldPair T) (e : x.curve = y.curve),
      x.P.1 ≫ eqToHom (congrArg projModelCR e) = y.P.1 →
      x.Q.1 ≫ eqToHom (congrArg projModelCR e) = y.Q.1 → x = y := by
  rintro ⟨xc, xP, xQ⟩ ⟨yc, yP, yQ⟩ e hP hQ
  cases e
  simp only [eqToHom_refl, Category.comp_id] at hP hQ
  obtain rfl : xP = yP := Subtype.ext hP
  obtain rfl : xQ = yQ := Subtype.ext hQ
  rfl

theorem section_eq_cast {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T] :
    ∀ {V₁ V₂ : WeierstrassCurve T} (e : V₁ = V₂) (P₁ : Section V₁) (P₂ : Section V₂)
      (χ₁ : OriginChartRing V₁ →+* T) (χ₂ : OriginChartRing V₂ →+* T),
      ReducesToOrigin P₁ χ₁ (maximalIdeal T) → ReducesToOrigin P₂ χ₂ (maximalIdeal T) →
      originParam χ₁ = originParam χ₂ → P₁.1 ≫ eqToHom (congrArg projModelCR e) = P₂.1 := by
  rintro V _ rfl P₁ P₂ χ₁ χ₂ h₁ h₂ h
  rw [eqToHom_refl, Category.comp_id]
  exact congrArg Subtype.val
    (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq V P₁ P₂ χ₁ χ₂ h₁ h₂ h).1

theorem reducesToOrigin_mono {T : Type u} [CommRing T] {V : WeierstrassCurve T} (P : Section V)
    (χ : OriginChartRing V →+* T) {I J : Ideal T} (hIJ : I ≤ J) (h : ReducesToOrigin P χ I) :
    ReducesToOrigin P χ J :=
  ⟨h.1, hIJ h.2.1, hIJ h.2.2⟩

end ModularCurve.LevelModuliPackageAbs.DrinPairEq

open ModularCurve.LevelModuliPackageAbs.DrinPairEq in
set_option maxHeartbeats 3200000 in

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
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χQ)) = y₁)
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1)
    (hCE : C • (x.curve.map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) = x.curve.map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) :
    𝒯.map ((φ₂.restrictScalars A₀).comp ι) x.level.2.2 = 𝒯.act C (𝒯.map ((φ₁.restrictScalars A₀).comp ι) x.level.2.2) := by
  obtain ⟨hφ₁, F₁, hbc₁, ψ₁, hψ₁, hψ₁P, hψ₁Q⟩ := h₁
  obtain ⟨hφ₂, F₂, hbc₂, ψ₂, hψ₂, hψ₂P, hψ₂Q⟩ := h₂

  rw [𝒯.map_comp, 𝒯.map_comp]
  have eY : 𝒯.map ι x.level.2.2 = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 := rfl
  rw [eY]
  have hcurve : (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve = x.curve.map ι.toRingHom :=
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).isLevel.1.2.2.1

  have hmono : ∀ (φ : R →ₐ[W₀] T), (∀ r, resT (φ r) = resR r) →
      (maximalIdeal R).map φ.toRingHom ≤ maximalIdeal T := by
    intro φ hφ
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← hkT, RingHom.mem_ker]
    show resT (φ r) = 0
    rw [hφ, ← RingHom.mem_ker, hkerR]
    exact hr
  have hmem : ∀ (φ : R →ₐ[W₀] T), (∀ r, resT (φ r) = resR r) → ∀ r ∈ maximalIdeal R, φ r ∈ maximalIdeal T :=
    fun φ hφ r hr ↦ hmono φ hφ (Ideal.mem_map_of_mem φ.toRingHom hr)

  have e : C • ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom) = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₂.toRingHom := by
    rw [hcurve]; simp only [WeierstrassCurve.map_map]; exact hCE

  obtain ⟨hact, hmap⟩ := h𝒯
  obtain ⟨hc₁, hpin₁⟩ := hmap _ _ (φ₁.restrictScalars A₀) (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2)
  obtain ⟨hc₂, hpin₂⟩ := hmap _ _ (φ₂.restrictScalars A₀) (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2)
  obtain ⟨hc₃, hpin₃⟩ := hact _ C (𝒯.map (φ₁.restrictScalars A₀) (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2))

  suffices main : ∀ (c₁ : WeierstrassCurve.Projective T) (P₁ Q₁ : Section c₁)
      (hc₁ : c₁ = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map (φ₁.restrictScalars A₀).toRingHom)
      (_ : ∀ (φ : projModelGradingCR (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve →+*ᵍ
              projModelGradingCR ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map (φ₁.restrictScalars A₀).toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map (φ₁.restrictScalars A₀).toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve)).map φ),
        IsCoefficientHom (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve (φ₁.restrictScalars A₀).toRingHom φ →
          P₁.1 ≫ eqToHom (congrArg projModelCR hc₁) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom (φ₁.restrictScalars A₀).toRingHom) ≫ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).P.1 ∧
          Q₁.1 ≫ eqToHom (congrArg projModelCR hc₁) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom (φ₁.restrictScalars A₀).toRingHom) ≫ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).Q.1)
      (c₂ : WeierstrassCurve.Projective T) (P₂ Q₂ : Section c₂)
      (hc₂ : c₂ = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map (φ₂.restrictScalars A₀).toRingHom)
      (_ : ∀ (φ : projModelGradingCR (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve →+*ᵍ
              projModelGradingCR ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map (φ₂.restrictScalars A₀).toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map (φ₂.restrictScalars A₀).toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve)).map φ),
        IsCoefficientHom (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve (φ₂.restrictScalars A₀).toRingHom φ →
          P₂.1 ≫ eqToHom (congrArg projModelCR hc₂) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom (φ₂.restrictScalars A₀).toRingHom) ≫ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).P.1 ∧
          Q₂.1 ≫ eqToHom (congrArg projModelCR hc₂) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom (φ₂.restrictScalars A₀).toRingHom) ≫ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).Q.1)
      (c₃ : WeierstrassCurve.Projective T) (P₃ Q₃ : Section c₃) (hc₃ : c₃ = C • c₁)
      (_ : ∀ (φ : projModelGradingCR c₁ →+*ᵍ projModelGradingCR (C • c₁))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • c₁)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR c₁)).map φ),
        IsVariableChangeHom c₁ C φ →
          P₃.1 ≫ eqToHom (congrArg projModelCR hc₃) ≫ Proj.map φ hφ = P₁.1 ∧
          Q₃.1 ≫ eqToHom (congrArg projModelCR hc₃) ≫ Proj.map φ hφ = Q₁.1),
      (⟨c₂, P₂, Q₂⟩ : RawDrinfeldPair T) = ⟨c₃, P₃, Q₃⟩ by
    exact main _ _ _ hc₁ hpin₁ _ _ _ hc₂ hpin₂ _ _ _ hc₃ hpin₃
  intro c₁ P₁ Q₁ hc₁ hpin₁ c₂ P₂ Q₂ hc₂ hpin₂ c₃ P₃ Q₃ hc₃ hpin₃
  subst hc₁ hc₂ hc₃

  obtain ⟨φc₁, hφc₁, hcoef₁⟩ := WeierstrassProjModel.exists_isCoefficientHom (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₁.toRingHom
  obtain ⟨φc₂, hφc₂, hcoef₂⟩ := WeierstrassProjModel.exists_isCoefficientHom (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₂.toRingHom
  obtain ⟨φv, hφv, hvc, -, -⟩ :=
    WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom) C
  obtain ⟨hP₁, hQ₁⟩ := hpin₁ φc₁ hφc₁ hcoef₁
  obtain ⟨hP₂, hQ₂⟩ := hpin₂ φc₂ hφc₂ hcoef₂
  obtain ⟨hP₃, hQ₃⟩ := hpin₃ φv hφv hvc
  simp only [eqToHom_refl, Category.id_comp] at hP₁ hQ₁ hP₂ hQ₂ hP₃ hQ₃

  obtain ⟨χ₁, hχ₁, hz₁, -⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
    (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₁.toRingHom φc₁ hφc₁ hcoef₁ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).P χP (maximalIdeal R) hP P₁ hP₁
  obtain ⟨χ₂, hχ₂, hz₂, -⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
    (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₂.toRingHom φc₂ hφc₂ hcoef₂ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).P χP (maximalIdeal R) hP P₂ hP₂
  obtain ⟨ξ₁, hξ₁, hw₁, -⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
    (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₁.toRingHom φc₁ hφc₁ hcoef₁ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).Q χQ (maximalIdeal R) hQ Q₁ hQ₁
  obtain ⟨ξ₂, hξ₂, hw₂, -⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
    (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₂.toRingHom φc₂ hφc₂ hcoef₂ (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).Q χQ (maximalIdeal R) hQ Q₂ hQ₂
  have hχ₁' := reducesToOrigin_mono P₁ χ₁ (hmono φ₁ hφ₁) hχ₁
  have hχ₂' := reducesToOrigin_mono P₂ χ₂ (hmono φ₂ hφ₂) hχ₂
  have hξ₁' := reducesToOrigin_mono Q₁ ξ₁ (hmono φ₁ hφ₁) hξ₁
  have hξ₂' := reducesToOrigin_mono Q₂ ξ₂ (hmono φ₂ hφ₂) hξ₂
  obtain ⟨χ₃, hχ₃, hz₃⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
    ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom) C φv hφv hvc P₁ χ₁ hχ₁' P₃ hP₃
  obtain ⟨ξ₃, hξ₃, hw₃⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
    ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom) C φv hφv hvc Q₁ ξ₁ hξ₁' Q₃ hQ₃

  have hG₁ : F₁.toPowerSeries = ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom).formalGroupLawFixed := by
    rw [(WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₁.toRingHom).2, ← hFW]; exact hbc₁
  have hG₂ : F₂.toPowerSeries = (C • ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom)).formalGroupLawFixed := by
    rw [e, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve φ₂.toRingHom).2, ← hFW]; exact hbc₂
  obtain ⟨σ, hσs⟩ := FormalGroup.exists_lawHom_series_eq_variableChangeSeries ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom) C F₁ F₂ hG₁ hG₂
  have hσ : PowerSeries.map resT σ.series = PowerSeries.X := by
    rw [hσs, ← (WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom) C resT).2,
      hC, WeierstrassCurve.variableChangeSeries_one]
  have hbF₁ : F₁.IsBaseChange resT F₀ := by
    show F₀.toPowerSeries = MvPowerSeries.map resT F₁.toPowerSeries
    have h1 : F₁.toPowerSeries = MvPowerSeries.map φ₁.toRingHom F.toPowerSeries := hbc₁
    rw [h1, MvPowerSeries.map_map, hF₀W, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve resR).2, hFW]
    congr 2
    exact (RingHom.ext hφ₁).symm
  have key : ∀ (a₁ a₂ : T), a₁ ∈ maximalIdeal T → a₂ ∈ maximalIdeal T →
      ψ₁.toLawHom.appAdic (maximalIdeal T) a₁ = ψ₂.toLawHom.appAdic (maximalIdeal T) a₂ →
      σ.appAdic (maximalIdeal T) a₁ = a₂ := fun a₁ a₂ ha₁ ha₂ h ↦
    FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X q resT hsT hkT F₀ hF₀ F₁ F₂ G hbF₁ hG
      ψ₁ ψ₂ hψ₁ hψ₂ σ hσ a₁ a₂ ha₁ ha₂ h
  have hzP : σ.appAdic (maximalIdeal T) (φ₁ (originParam χP)) = φ₂ (originParam χP) :=
    key _ _ (hmem φ₁ hφ₁ _ hP.2.1) (hmem φ₂ hφ₂ _ hP.2.1) (hψ₁P.trans hψ₂P.symm)
  have hzQ : σ.appAdic (maximalIdeal T) (φ₁ (originParam χQ)) = φ₂ (originParam χQ) :=
    key _ _ (hmem φ₁ hφ₁ _ hQ.2.1) (hmem φ₂ hφ₂ _ hQ.2.1) (hψ₁Q.trans hψ₂Q.symm)
  have happ : ∀ a : T, σ.appAdic (maximalIdeal T) a =
      (letI : WithIdeal T := ⟨maximalIdeal T⟩;
        FormalGroup.evalSeries (((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.map φ₁.toRingHom).variableChangeSeries C) a) := by
    intro a; rw [← hσs]; rfl
  have hparP : originParam χ₂ = originParam χ₃ := by
    rw [hz₃, hz₁, hz₂, ← happ]; exact hzP.symm
  have hparQ : originParam ξ₂ = originParam ξ₃ := by
    rw [hw₃, hw₁, hw₂, ← happ]; exact hzQ.symm

  refine rawDrinfeldPair_ext _ _ e.symm ?_ ?_
  · exact section_eq_cast e.symm P₂ P₃ χ₂ χ₃ hχ₂' hχ₃ hparP
  · exact section_eq_cast e.symm Q₂ Q₃ ξ₂ ξ₃ hξ₂' hξ₃ hparQ

end S_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow (solution)
