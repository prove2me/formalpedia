-- Prove2me | solution 1 for GlobalTheory.isPullback_equalizer_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:48.709952+00:00
-- url     : https://prove2.me/submissions/8e2624dd-50a9-4a5b-b71b-ad1e0dcedad7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

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
theorem _root_.solution {X S T : Scheme.{u}} (f : X ⟶ S) {a b : T ⟶ X}
    (hab : a ≫ f = b ≫ f) :
    IsPullback (equalizer.ι a b ≫ a) (equalizer.ι a b) (pullback.diagonal f)
      (pullback.lift a b hab) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ equalizer.lift s.snd ?_) ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · simp [pullback.lift_fst]
    · simpa [pullback.lift_snd] using equalizer.condition a b
  · have h1 := s.condition =≫ pullback.fst _ _
    have h2 := s.condition =≫ pullback.snd _ _
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [← h1, h2]
  · intro s
    have h1 := s.condition =≫ pullback.fst _ _
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      pullback.lift_fst] at h1
    simp [h1]
  · intro s
    simp
  · intro s m _ h
    rw [← cancel_mono (equalizer.ι a b), h]
    simp
end GlobalTheory
