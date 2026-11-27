-- Prove2me | solution 1 for GlobalTheory.existsUnique_normalization_to_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:13.521415+00:00
-- url     : https://prove2.me/submissions/42f51808-2061-4ca7-99a5-6eda51d05d55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_flat_normalization_of_fractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [IsDedekindDomain R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] {R₀ : Type u} [CommRing R₀] [Algebra R₀ R]
    [Algebra.IsIntegral R₀ R] (s : Y ⟶ Spec (.of R₀)) (c : X ⟶ Spec (.of K))
    (hc : f ≫ s = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) :
    (∃! p : f.normalization ⟶ Spec (.of R),
      f.toNormalization ≫ p = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    ∀ p : f.normalization ⟶ Spec (.of R),
      f.toNormalization ≫ p = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) →
        Flat p ∧ p ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ R)) = f.fromNormalization ≫ s := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  refine ⟨⟨normalizationLift f (c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) s (by simpa using hc.symm), by simp, fun p hp ↦ ?_⟩,
    fun p hp ↦ ⟨flat_normalization_of_fractionRing f K p c hp, ?_⟩⟩
  · exact normalization_hom_ext f (terminal.from _) (by simp [hp]) (terminal.hom_ext _ _)
  · exact normalization_hom_ext f (terminal.from _) (by simp [reassoc_of% hp, hc])
      (terminal.hom_ext _ _)
end GlobalTheory
