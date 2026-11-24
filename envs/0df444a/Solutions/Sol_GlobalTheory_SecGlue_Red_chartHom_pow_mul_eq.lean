-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.chartHom_pow_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:42.436269+00:00
-- url     : https://prove2.me/submissions/3f1d4d1d-6507-42e8-949d-bb00f6e9a197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
import Theorems.Thm_GlobalTheory_T_exists_pow_mul_eq_of_algebraMap_localizationAway_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {R : Type} [CommRing R] (X : Over (Sp R)) (hsm : Smooth X.hom)
    (W : X.left.Opens) (hW : IsAffineOpen W) {S : Type} [CommRing S] (u₁ u₂ : Sp S ⟶ X.left)
    (hu : u₁ ≫ X.hom = u₂ ≫ X.hom) (h₁ : u₁ ⁻¹ᵁ W = ⊤) (h₂ : u₂ ⁻¹ᵁ W = ⊤) (g : S)
    (hg : ∀ x, algebraMap S (Localization.Away g) (chartHom W u₁ h₁ x) =
      algebraMap S (Localization.Away g) (chartHom W u₂ h₂ x)) :
    ∃ M : ℕ, ∀ x, g ^ M * chartHom W u₁ h₁ x = g ^ M * chartHom W u₂ h₂ x := by
  have hle : W ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  let b := (X.hom.appLE ⊤ W hle).hom
  have hft : b.FiniteType := by
    haveI := hsm
    exact HasRingHomProperty.appLE @LocallyOfFiniteType X.hom inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  have hcomp : ∀ (u : Sp S ⟶ X.left) (h : u ⁻¹ᵁ W = ⊤),
      (chartHom W u h).comp b = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp
        (u ≫ X.hom).appTop.hom := by
    intro u h
    have e : (u ≫ X.hom).appTop = (u ≫ X.hom).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [e, ← Scheme.Hom.appLE_comp_appLE u X.hom ⊤ W ⊤ hle h.ge]
    rfl
  letI : Algebra Γ(Sp R, ⊤) Γ(X.left, W) := b.toAlgebra
  letI : Algebra Γ(Sp R, ⊤) S := ((chartHom W u₁ h₁).comp b).toAlgebra
  haveI : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X.left, W) := hft
  let χ₁ : Γ(X.left, W) →ₐ[Γ(Sp R, ⊤)] S := { chartHom W u₁ h₁ with commutes' := fun r => rfl }
  let χ₂ : Γ(X.left, W) →ₐ[Γ(Sp R, ⊤)] S :=
    { chartHom W u₂ h₂ with
      commutes' := fun r => by
        have := congrArg (fun φ : Γ(Sp R, ⊤) →+* S => φ r) ((hcomp u₂ h₂).trans (hu ▸ (hcomp u₁ h₁).symm))
        exact this }
  exact GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq _ _ _ χ₁ χ₂ g hg
end GlobalTheory.SecGlue.Red
