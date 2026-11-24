-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_section_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:01.911367+00:00
-- url     : https://prove2.me/submissions/82051dae-74dc-496d-804d-23be2e04ef4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsOpenImmersion s := by
  have hab : (𝟙 X) ≫ f = (f ≫ s) ≫ f := by simp [hs]
  have := isOpenImmersion_equalizer_ι_of_unramified f hab
  have h1 : s ≫ 𝟙 X = s ≫ f ≫ s := by simp [reassoc_of% hs]
  have h2 := equalizer.condition (𝟙 X) (f ≫ s)
  have : IsIso (equalizer.lift s h1) := ⟨equalizer.ι _ _ ≫ f, by simp [hs], by
    rw [← cancel_mono (equalizer.ι _ _)]
    simpa using h2.symm⟩
  rw [← equalizer.lift_ι s h1]
  infer_instance
end GlobalTheory
