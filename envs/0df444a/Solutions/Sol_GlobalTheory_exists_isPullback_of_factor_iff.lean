-- Prove2me | solution 1 for GlobalTheory.exists_isPullback_of_factor_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:36.2668+00:00
-- url     : https://prove2.me/submissions/f4143ff2-30fc-49ad-a282-2e403caf000d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {C : Type*} [Category C] {X X' A B : C} (m : X' ⟶ X)
    (b : B ⟶ X) (a : A ⟶ X') [Mono a] [Mono b]
    (h : ∀ (Y : C) (g : Y ⟶ X'), (∃ z : Y ⟶ B, z ≫ b = g ≫ m) ↔ (∃ z : Y ⟶ A, z ≫ a = g)) :
    ∃ k : A ⟶ B, IsPullback k a b m := by
  obtain ⟨k, hk⟩ := (h A a).2 ⟨𝟙 A, Category.id_comp a⟩
  refine ⟨k, ⟨hk⟩, ⟨PullbackCone.IsLimit.mk hk
    (fun s => ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
  · intro s
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono b, Category.assoc, hk, ← Category.assoc, hs, s.condition]
  · intro s
    exact ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
  · intro s l _ hl
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono a, hl, hs]
end GlobalTheory
