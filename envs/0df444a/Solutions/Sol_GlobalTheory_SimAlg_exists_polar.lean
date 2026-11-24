-- Prove2me | solution 1 for GlobalTheory.SimAlg.exists_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:08.782129+00:00
-- url     : https://prove2.me/submissions/f0d8bdef-9098-4711-a42f-125a6ed3d237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution {Λ : Type} [AddCommGroup Λ] (Q : Λ → ℤ)
    (h : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) :
    ∃ b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x y, b x y = Q (x + y) - Q x - Q y) ∧ ∀ x, b x x = 2 * Q x := by
  have h0 : Q 0 = 0 := by have := h 0 0; simp at this; omega
  have h3 : ∀ x y z, Q (x + y + z) = Q (x + y) + Q (x + z) + Q (y + z) - Q x - Q y - Q z := by
    intro x y z
    have a1 := h (x + y) z
    have a2 := h (x + z) y
    have a3 := h x (y - z)
    have a4 := h y z
    rw [show x + z + y = x + y + z by abel] at a2
    rw [show x + (y - z) = x + y - z by abel, show x - (y - z) = x + z - y by abel] at a3
    omega
  let b0 : Λ →+ Λ →+ ℤ := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Q (x + y) - Q x - Q y)
    (by intro y z; rw [← add_assoc, h3]; ring)) (by
      intro x y; ext z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [h3]; ring)
  refine ⟨LinearMap.mk₂ ℤ (fun x y => b0 x y) (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp), fun x y => rfl, fun x => ?_⟩
  have := h x x
  rw [sub_self, h0] at this
  change Q (x + x) - Q x - Q x = _
  omega
end GlobalTheory.SimAlg
