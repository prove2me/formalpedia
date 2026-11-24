-- Prove2me | solution 1 for GlobalTheory.PosFormAdjoint.int_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:28:18.091034+00:00
-- url     : https://prove2.me/submissions/a9a17350-13b0-4de5-a7c8-d634049f6fa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosSemidefQuadraticAdjointPairBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PosFormAdjoint
namespace GlobalTheory.PosFormAdjoint
theorem _root_.solution {X : Type} [AddCommGroup X] (F : X →+ X →+ ℤ)
    (hsym : ∀ u v, F u v = F v u) (hpos : ∀ u, 0 ≤ F u u) (u v : X) :
    F u v ^ 2 ≤ F u u * F v v := by
  have key : ∀ a b : ℤ, 0 ≤ a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
    intro a b
    have h1 := hpos (a • u + b • v)
    have e : F (a • u + b • v) (a • u + b • v)
        = a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
      simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
      rw [hsym v u]
      ring
    rw [e] at h1
    exact h1
  rcases (hpos u).lt_or_eq with ht | ht
  · have h2 := key (-(F u v)) (F u u)
    have h3 : 0 ≤ F u u * (F u u * F v v - F u v ^ 2) := by nlinarith [h2]
    have h4 : 0 ≤ F u u * F v v - F u v ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_neg_of_pos_of_neg ht hc]
    linarith
  · rw [← ht]
    simp only [zero_mul]
    by_contra hc
    push_neg at hc
    have hs : (1 : ℤ) ≤ F u v ^ 2 := hc
    have h2 := key (-(F v v + 1) * F u v) 1
    rw [← ht] at h2
    have hv := hpos v
    nlinarith [h2, hs, hv]
end GlobalTheory.PosFormAdjoint
