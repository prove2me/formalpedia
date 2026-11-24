-- Prove2me | solution 1 for GlobalTheory.over_points_ext_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:42.890404+00:00
-- url     : https://prove2.me/submissions/874155fe-2f2c-46ec-8882-33103ba63d21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_OverPointsExtOfInjective
import Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_schemeDominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (G : Over S) [IsSeparated G.hom]
    (W F : Type) [CommRing W] [CommRing F] (φ : W →+* F) (hφ : Function.Injective φ)
    (p : Spec (CommRingCat.of W) ⟶ S) (y y' : Over.mk p ⟶ G)
    (h : (Spec.map (CommRingCat.ofHom φ)) ≫ y.left = (Spec.map (CommRingCat.ofHom φ)) ≫ y'.left) :
    y = y' := by
  let d : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  have hd : d ≫ y = d ≫ y' := by
    ext1
    simpa [d] using h
  let l := equalizer.lift d hd
  have hl : l ≫ equalizer.ι y y' = d := equalizer.lift_ι d hd
  have hfac : l.left ≫ (equalizer.ι y y').left = Spec.map (CommRingCat.ofHom φ) := by
    rw [← Over.comp_left, hl]
    rfl
  have hdom : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) :=
    (_root_.GlobalTheory.schemeDominant_specMap_iff _).2 (by simpa using hφ)
  have hdomι : IsSchemeTheoreticallyDominant (equalizer.ι y y').left :=
    ⟨eq_bot_iff.2 ((Scheme.Hom.le_ker_comp l.left _).trans (by rw [hfac, hdom.ker_eq_bot]))⟩
  have hiso : IsIso (equalizer.ι y y').left :=
    _root_.GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant _
  ext1
  rw [← cancel_epi (equalizer.ι y y').left, ← Over.comp_left, ← Over.comp_left,
    equalizer.condition]
end _root_.GlobalTheory
end GlobalTheory
