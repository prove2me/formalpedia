-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ed5cb714-feae-51fb-b973-117a09f44140

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem solution
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ N : ℕ)
    (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢₀ : GroupLaws A₀) (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum)
    (P : LevelModuliPackageAbs A
      (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
    (φ : P₀.B₀ →+* P.B₀)

    (hφ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
        (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
        (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p))
        (hD : ModularCurve.IsLevelPStructure W ℓ D)
        (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z),
        letI : Algebra A₀ T := algebraRestrict A₀ A T
        (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
            ((gamma0PowComponent A N hM).prod ((levelPComponent A ℓ hℓ).prod
              (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).Raw T))).toRingHom.comp φ =
        (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
            ((gamma0PowComponent A₀ N hM₀).prod ((levelPComponent A₀ ℓ hℓ₀).prod
              (levelComponent A₀ 𝒢₀ q 𝒯₀))).Raw T))).toRingHom)
    (T : Type u) [CommRing T] [Algebra A T] :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    ∀ x : (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.Pt T,
      ∃ x' : (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.Pt T,
        (rigidDataPow A ℓ N q hℓ hM (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum.jOf x' =
          (rigidDataPow A₀ ℓ N q hℓ₀ hM₀ 𝒢₀ 𝒯₀).toLevelModuliDatum.jOf x ∧
        (P.classify x').toRingHom.comp φ = (P₀.classify x).toRingHom := by
  letI instA₀T : Algebra A₀ T := algebraRestrict A₀ A T
  intro x

  obtain ⟨r, rfl⟩ := Quot.exists_rep x
  obtain ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ := r

  refine ⟨Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ :
      ((gamma0PowComponent A N hM).prod ((levelPComponent A ℓ hℓ).prod
        (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).Raw T), ?_, ?_⟩
  ·
    rfl
  ·
    exact hφ T W hΔ h D z hh hD hz

end S_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_pt_restrictScalars_jOf_eq_classify_comp_eq_gamma0Pow (solution)
