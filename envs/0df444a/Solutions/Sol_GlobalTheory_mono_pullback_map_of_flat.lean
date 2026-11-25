-- Prove2me | solution 1 for GlobalTheory.mono_pullback_map_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:00.834961+00:00
-- url     : https://prove2.me/submissions/fa3197ec-c429-4d89-8f4a-f6363833c83b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlat
import Theorems.Thm_GlobalTheory_SkyMod_nonempty_adjunction
import Theorems.Thm_GlobalTheory_SkyMod_nonempty_sky_pushforward_iso
import Theorems.Thm_GlobalTheory_QCoh_mono_iff_stalkLinear_injective
import Theorems.Thm_GlobalTheory_QCoh_stalkLinear_injective


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
namespace GlobalTheory
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules)
    (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by
  intro X Y f _ G G' φ _
  rw [GlobalTheory.QCoh.mono_iff_stalkLinear_injective]
  intro x
  obtain ⟨a₁⟩ := GlobalTheory.SkyMod.nonempty_adjunction X x
  obtain ⟨a₂⟩ := GlobalTheory.SkyMod.nonempty_adjunction Y (f x)
  obtain ⟨e⟩ := GlobalTheory.SkyMod.nonempty_sky_pushforward_iso X Y f x
  let adjA := ((Scheme.Modules.pullbackPushforwardAdjunction f).comp a₁).ofNatIsoRight e
  let adjB := a₂.comp (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
  let iso := adjA.leftAdjointUniq adjB
  have hn := iso.hom.naturality φ
  have hφ : Function.Injective (GlobalTheory.QCoh.stalkLinear φ (f x)) := GlobalTheory.QCoh.stalkLinear_injective φ (f x)
  letI := (f.stalkMap x).hom.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have hext : Function.Injective ((ModuleCat.extendScalars (f.stalkMap x).hom).map
      ((stalkFunctor (f x)).map φ)) := by
    change Function.Injective (LinearMap.baseChange _ (GlobalTheory.QCoh.stalkLinear φ (f x)))
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ
  have h2 : Function.Injective (((Functor.comp (Scheme.Modules.pullback f) (stalkFunctor x)).map φ ≫
      iso.hom.app G').hom) := by
    rw [hn, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact hext.comp (iso.app G).toLinearEquiv.injective
  rw [ModuleCat.hom_comp, LinearMap.coe_comp] at h2
  exact Function.Injective.of_comp h2
end GlobalTheory
