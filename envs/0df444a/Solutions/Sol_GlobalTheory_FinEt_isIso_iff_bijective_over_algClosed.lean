-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_iff_bijective_over_algClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:51.008544+00:00
-- url     : https://prove2.me/submissions/747a22a4-df90-4923-8370-12b3386d2bfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_iff_bijective_algClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      Function.Bijective fun x : Over.mk s ⟶ X ↦ x ≫ f := by
  have := isFinite_left f
  have := etale_left f
  constructor
  · intro _ k _ _ s
    exact ⟨fun a b h ↦ (cancel_mono f).mp h, fun y ↦ ⟨y ≫ inv f, by simp⟩⟩
  intro h
  rw [isIso_iff_isIso_left, isIso_iff_bijective_algClosed]
  intro k _ _
  constructor
  · intro a b (hab : a ≫ f.left = b ≫ f.left)
    have hb : b ≫ X.hom = a ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← hab, Category.assoc]
    have := (h k (a ≫ X.hom)).1 (a₁ := Over.homMk a rfl) (a₂ := Over.homMk b hb)
      (Over.OverMorphism.ext hab)
    exact congr(($this).left)
  · intro y
    obtain ⟨x, hx⟩ := (h k (y ≫ Y.hom)).2 (Over.homMk y rfl)
    exact ⟨x.left, congr(($hx).left)⟩
end GlobalTheory.FinEt
