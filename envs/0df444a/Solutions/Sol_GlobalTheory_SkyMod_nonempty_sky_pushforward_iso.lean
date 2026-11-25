-- Prove2me | solution 1 for GlobalTheory.SkyMod.nonempty_sky_pushforward_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:50.118327+00:00
-- url     : https://prove2.me/submissions/f2eb47e3-6d90-4d47-a84c-799dff3eaa2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory.SkyMod
namespace GlobalTheory.SkyMod
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (x : X), Nonempty (GlobalTheory.SkyMod.skyFunctor x ⋙ Scheme.Modules.pushforward f ≅ ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ GlobalTheory.SkyMod.skyFunctor (f x)) := by
  intro X Y f x
  have key : ∀ (M : ModuleCat.{0} (X.presheaf.stalk x)) (U : Y.Opens) (r : Γ(Y, U))
      (m : Obj x (f ⁻¹ᵁ U) M) (h : PLift (f x ∈ U)),
      X.presheaf.germ (f ⁻¹ᵁ U) x h.down (f.app U r) • m h =
        f.stalkMap x (Y.presheaf.germ U (f x) h.down r) • m h := fun M U r m h ↦ by
    rw [Scheme.Hom.germ_stalkMap_apply]
  refine ⟨NatIso.ofComponents (fun M ↦ ⟨⟨PresheafOfModules.homMk (𝟙 _)
      (fun U r m ↦ funext fun h ↦ key M U.unop r m h)⟩,
    ⟨PresheafOfModules.homMk (𝟙 _) (fun U r m ↦ funext fun h ↦ (key M U.unop r m h).symm)⟩,
    rfl, rfl⟩) (fun g ↦ rfl)⟩
end GlobalTheory.SkyMod
