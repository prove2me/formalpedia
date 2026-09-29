-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/19649656-16bf-5050-b226-ee0e9d9649cc

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
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

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
    [(((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).IsElliptic] :
    F.IsBaseChange resR F₀ ∧
      ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map (IsLocalRing.residue R)).formalGroup.IsDrinfeldBasisAdic
        ⊥ q 0 0 :=by
  set E := ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve with hE
  have hmapR := (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E resR).2
  refine ⟨?_, ?_⟩
  ·
    show F₀.toPowerSeries = MvPowerSeries.map resR F.toPowerSeries
    rw [hF₀W, hFW, hmapR]
  ·

    let e : R ⧸ RingHom.ker resR ≃+* k := RingHom.quotientKerEquivOfSurjective hresR
    let e' : ResidueField R ≃+* k := (Ideal.quotEquivOfEq hkerR.symm).trans e
    have he' : ∀ r : R, e' (IsLocalRing.residue R r) = resR r := by
      intro r
      show e (Ideal.quotEquivOfEq hkerR.symm (Ideal.Quotient.mk (maximalIdeal R) r)) = resR r
      rw [Ideal.quotEquivOfEq_mk]
      exact RingHom.quotientKerEquivOfSurjective_apply_mk hresR r
    let g : k →+* ResidueField R := (e'.symm : k ≃+* ResidueField R)
    have hg : (g.comp resR) = IsLocalRing.residue R := by
      ext r
      show e'.symm (resR r) = IsLocalRing.residue R r
      rw [← he' r, RingEquiv.symm_apply_apply]

    have hbc : F₀.IsBaseChange g (E.map (IsLocalRing.residue R)).formalGroup := by
      show (E.map (IsLocalRing.residue R)).formalGroup.toPowerSeries = MvPowerSeries.map g F₀.toPowerSeries
      have h1 : (E.map (IsLocalRing.residue R)).formalGroup.toPowerSeries =
          (E.map (IsLocalRing.residue R)).formalGroupLawFixed := rfl
      rw [h1, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E (IsLocalRing.residue R)).2, hF₀W, hmapR,
        ← hg, MvPowerSeries.map_map]
    have := FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange (⊥ : Ideal k) (⊥ : Ideal (ResidueField R)) g
      (fun r hr => by simp [(Ideal.mem_bot).mp hr]) F₀ _ hbc q 0 0 (Ideal.zero_mem _) (Ideal.zero_mem _) hF₀
    simpa using this

end S_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow (solution)
