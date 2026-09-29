-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_pow_of_factorsThrough_of_five_le_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2e1e0bad-f8e1-598e-8b3c-d3cb3944745d

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
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le
import Theorems.Thm_WeierstrassCurve_jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
import Theorems.Thm_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_universal_deformation_powerSeries_of_generic_lift
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_isBaseChange_lawIso
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_pow_of_factorsThrough_of_five_le_gamma0Pow
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing IsLocalRing.SmallExtension.algebra"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' IsLocalRing.SmallExtension.snd_pair IsLocalRing.SmallExtension.res_mk IsLocalRing.SmallExtension.snd_apply IsLocalRing.SmallExtension.coe_diag IsLocalRing.SmallExtension.fst_pair IsLocalRing.SmallExtension.fst_apply FormalGroup.ofPair_toPowerSeries IsLocalRing.SmallExtension.mk_thetaLiftAlgHom FormalGroup.LawIso.map_series IsLocalRing.SmallExtension.fst_pairRingHom FormalGroup.LawIso.ofPair_series FormalGroup.LawHom.ofPair_series IsLocalRing.SmallExtension.snd_pairRingHom IsLocalRing.SmallExtension.snd_pairAlgHom IsLocalRing.SmallExtension.fst_pairAlgHom FormalGroup.LawHom.map_series IsLocalRing.SmallExtension.fst_thetaLift IsLocalRing.SmallExtension.mk_thetaLift IsLocalRing.SmallExtension.fst_thetaLiftAlgHom"

set_option autoImplicit false

universe u

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup~map_map"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq5 : 5 ≤ q) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
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
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0) :
    ∃ (T : R) (w : R) (_ : IsUnit w)
      (_ : PowerSeries.coeff q (F.nthSeries q) - w * T ∈ Ideal.span {(q : R)})
      (a₀ : W₀) (k : ℕ) (_ : 1 ≤ k) (w' : R) (_ : IsUnit w'),
      ι P₀.j₀ - algebraMap W₀ R a₀ = w' * T ^ k := by
  classical

  set xR := (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x with hxR
  have hEcurve : (xR.level.2.2.curve : WeierstrassCurve R) = xR.curve := xR.isLevel.2.2.1
  have hΔR : IsUnit (xR.curve).Δ := xR.isUnit_Δ
  set E₀ : WeierstrassCurve k := xR.curve.map resR with hE₀
  have hΔ₀ : IsUnit E₀.Δ := xR.curve.isUnit_Δ_map resR hΔR
  haveI hE₀ell : E₀.IsElliptic := ⟨hΔ₀⟩

  have hFW' : F.toPowerSeries = xR.curve.formalGroupLawFixed := by rw [← hEcurve]; exact hFW
  have hF₀W' : F₀.toPowerSeries = E₀.formalGroupLawFixed := by rw [hE₀, ← hEcurve]; exact hF₀W
  have hF₀eq : F₀ = E₀.formalGroup := FormalGroup.ext hF₀W'
  have hE₀ss : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0 := hF₀eq ▸ hF₀
  have hF : F.IsBaseChange resR F₀ := by
    show F₀.toPowerSeries = MvPowerSeries.map resR F.toPowerSeries
    rw [hF₀W', hFW', hE₀]
    exact (xR.curve.formalW_map_and_formalGroupLawFixed_map resR).2

  obtain ⟨𝓔, h𝓔Δ, h𝓔₀, Fu, hFuC, hFuW, hFu, hγ, u₁, hu₁, hH, a₀, e, he, u₂, hu₂, hj⟩ :=
    WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le
      q hq5 k E₀ hE₀ss W₀ hW₀ res₀ hres₀ hker₀
  haveI := hFuC
  have hFu' : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀ := by
    rw [hF₀eq]; exact hFu

  have hLT := FormalGroup.IsDrinfeldBasisAdic.universal_deformation_powerSeries_of_generic_lift
    q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu' hγ
  obtain ⟨φ, hφres, hφX, F', hF', ψ, hψ⟩ :=
    FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_isBaseChange_lawIso
      q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ R resR hresR hkerR hresR₀ F hF Fu hFu' hLT

  have hF'W : F'.toPowerSeries = (𝓔.map φ.toRingHom).formalGroupLawFixed := by
    have h1 : F'.toPowerSeries = MvPowerSeries.map φ.toRingHom Fu.toPowerSeries := hF'
    rw [h1, hFuW]; exact (𝓔.formalW_map_and_formalGroupLawFixed_map φ.toRingHom).2.symm
  haveI hF'C : F'.IsComm := ⟨by
    show F'.toPowerSeries = F'.toPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0]
    rw [hF'W]; exact (𝓔.map φ.toRingHom).formalGroupLawFixed_comm_of_commRing⟩

  obtain ⟨w₃, hw₃, hC⟩ :=
    FormalGroup.exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso q F F' ψ
  have hbc : F'.nthSeries q = PowerSeries.map φ.toRingHom (Fu.nthSeries q) :=
    FormalGroup.IsBaseChange.nthSeries_eq_map Fu φ.toRingHom F' hF' q
  have hcoeff : PowerSeries.coeff q (F'.nthSeries q) = φ (PowerSeries.coeff q (Fu.nthSeries q)) := by
    rw [hbc, PowerSeries.coeff_map]; rfl
  obtain ⟨r₁, hr₁⟩ := Ideal.mem_span_singleton'.mp hC
  obtain ⟨r₂, hr₂⟩ := Ideal.mem_span_singleton'.mp hH
  have hr₂' : φ r₂ * (q : R) = φ (PowerSeries.coeff q (Fu.nthSeries q)) - φ u₁ * φ PowerSeries.X := by
    have := congrArg φ hr₂
    simpa [map_mul, map_sub, map_natCast] using this

  have hj₀ : ι P₀.j₀ = xR.curve.jOfUnit hΔR := by
    have hm := (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf_map ι P₀.univ
    rw [LevelModuliPackageAbs.j₀, ← hm, ← hx]
    rfl
  have hred : (𝓔.map φ.toRingHom).map resR = E₀ := by
    rw [WeierstrassCurve.map_map]
    have : resR.comp φ.toRingHom = res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) := by
      ext r; exact hφres r
    rw [this]; exact h𝓔₀
  have hΔφ : IsUnit (𝓔.map φ.toRingHom).Δ := 𝓔.isUnit_Δ_map φ.toRingHom h𝓔Δ
  have hB := WeierstrassCurve.jOfUnit_eq_jOfUnit_of_lawIso_of_isAdicComplete
    q hq2 k E₀ hE₀ss R resR hresR hkerR (𝓔.map φ.toRingHom) xR.curve hred hE₀.symm hΔφ hΔR
    F' hF'W F hFW' ψ hψ
  have hjφ : (𝓔.map φ.toRingHom).jOfUnit hΔφ = φ (𝓔.jOfUnit h𝓔Δ) :=
    𝓔.jOfUnit_map φ.toRingHom h𝓔Δ hΔφ

  refine ⟨φ PowerSeries.X, w₃ * φ u₁, hw₃.mul (hu₁.map φ), ?_, a₀, e, he, φ u₂, hu₂.map φ, ?_⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨r₁ + w₃ * φ r₂, ?_⟩
    rw [hcoeff] at hr₁
    linear_combination hr₁ + w₃ * hr₂'
  · rw [hj₀, ← hB, hjφ]
    have hj' : 𝓔.jOfUnit h𝓔Δ = algebraMap W₀ (PowerSeries W₀) a₀ + u₂ * PowerSeries.X ^ e := by
      rw [← hj]; ring
    rw [hj', map_add, map_mul, map_pow, AlgHom.commutes]
    ring

end S_ModularCurve_LevelModuliPackageAbs_exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_pow_of_factorsThrough_of_five_le_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_pow_of_factorsThrough_of_five_le_gamma0Pow (solution)
