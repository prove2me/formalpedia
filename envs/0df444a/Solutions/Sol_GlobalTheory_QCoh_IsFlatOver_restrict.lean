-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFlatOver.restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:10:50.328643+00:00
-- url     : https://prove2.me/submissions/449f29ea-1d35-490d-89b4-4ab5b5123d9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable {ρ}
namespace GlobalTheory.QCoh
namespace IsFlatOver
theorem _root_.solution (h : IsFlatOver F ρ) {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] : IsFlatOver (F.restrict g) (g.appTop.hom.comp ρ) := by
  intro W hW
  letI := baseModule (F.restrict g) W (g.appTop.hom.comp ρ)
  letI := baseModule F (g ''ᵁ W) ρ
  haveI : Module.Flat R Γ(F, g ''ᵁ W) := h _ (hW.image_of_isOpenImmersion g)
  have key (r : R) : (g.appIso W).hom (baseHom (g ''ᵁ W) ρ r) =
      baseHom W (g.appTop.hom.comp ρ) r := by
    have : X.presheaf.map (homOfLE (le_top : g ''ᵁ W ≤ ⊤)).op ≫ (g.appIso W).hom =
        g.appTop ≫ Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
      rfl
    exact congr($this (ρ r))
  let l : Γ(F, g ''ᵁ W) →ₗ[R] Γ(F.restrict g, W) :=
    { toFun := (F.restrictAppIso g W).inv
      map_add' := map_add _
      map_smul' := fun r s ↦ (F.smul_restrictAppIso_inv_apply g W (baseHom _ ρ r) s).trans
        (congrArg (· • (F.restrictAppIso g W).inv s) (key r)) }
  exact .of_linearEquiv (LinearEquiv.ofBijective l
    (ConcreteCategory.bijective_of_isIso (F.restrictAppIso g W).inv)).symm
end IsFlatOver
end GlobalTheory.QCoh
