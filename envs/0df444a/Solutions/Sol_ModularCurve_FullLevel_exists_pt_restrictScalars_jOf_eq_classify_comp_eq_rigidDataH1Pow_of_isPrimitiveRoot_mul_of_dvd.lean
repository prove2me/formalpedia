-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/81b70edc-38ca-5254-9de2-ff2b4384c123

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem solution
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ N : ℕ)
    (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢₀ : GroupLaws A₀) (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum)
    (P : LevelModuliPackageAbs A
      (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
    (φ : P₀.B₀ →+* P.B₀)

    (hφ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
          (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p)) (hD : ModularCurve.IsGamma1Point W ℓ D)
          (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z) (hlk : ModularCurve.IsGamma1Link W ℓ N h D),
          letI : Algebra A₀ T := algebraRestrict A₀ A T
          (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A N hM).prod ((gamma1Component A ℓ hℓ).prod
                (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom.comp φ =
          (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A₀ N hM₀).prod ((gamma1Component A₀ ℓ hℓ₀).prod
                (levelComponent A₀ 𝒢₀ q 𝒯₀))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL₀ _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom)
    (T : Type u) [CommRing T] [Algebra A T] :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    ∀ x : (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.Pt T,
      ∃ x' : (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.Pt T,
        (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.jOf x' =
          (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.jOf x ∧
        (P.classify x').toRingHom.comp φ = (P₀.classify x).toRingHom := by
  letI instA₀T : Algebra A₀ T := algebraRestrict A₀ A T
  intro x

  obtain ⟨r, rfl⟩ := Quot.exists_rep x
  obtain ⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ := r

  refine ⟨Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
      (((gamma0PowComponent A N hM).prod ((gamma1Component A ℓ hℓ).prod
                (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).Raw T), ?_, ?_⟩
  ·
    rfl
  ·
    exact hφ T W hΔ h D z hh hD hz hlk

end S_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_rigidDataH1Pow_of_isPrimitiveRoot_mul_of_dvd (solution)
