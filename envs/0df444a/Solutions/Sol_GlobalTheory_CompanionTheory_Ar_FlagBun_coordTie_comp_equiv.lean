-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.coordTie_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:32:00.204348+00:00
-- url     : https://prove2.me/submissions/3cc45394-e482-421a-ba56-817d4b9654d3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
open AlgebraicGeometry CategoryTheory
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.FlagBun
theorem _root_.solution {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type}
    [CommRing o] [Algebra o Ω] {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' ≃ κ) :
    CoordTie o ξ (x ∘ e) := by
  have hch : ∀ c p, InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
    intro c p
    simp only [InChart, Function.comp]
    exact and_congr Iff.rfl ⟨fun h c' => by simpa using h (e.symm c'), fun h c' => h (e c')⟩
  have hr : ∀ c, Set.range (fun j => (x ∘ e) j / (x ∘ e) c) = Set.range (fun j => x j / x (e c)) := by
    intro c
    ext a
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (hch _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => by rw [hq q]; exact exists_congr fun h' => (hch c _).symm⟩
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (hch c p).symm Iff.rfl
end GlobalTheory.CompanionTheory.Ar.FlagBun
