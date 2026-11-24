-- Prove2me | solution 1 for GlobalTheory.IsSymplecticFamily.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:11.268832+00:00
-- url     : https://prove2.me/submissions/220568bd-e7c3-4c55-b6ad-69055acd58bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.IsSymplecticFamily
variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}
namespace GlobalTheory.IsSymplecticFamily
theorem _root_.solution {κ : Type*} {e' f' : κ → M} {d' : κ → R} (hB : B.IsAlt)
    (h : IsSymplecticFamily B e f d) (h' : IsSymplecticFamily B e' f' d')
    (h₁ : ∀ i j, B (e i) (e' j) = 0) (h₂ : ∀ i j, B (e i) (f' j) = 0)
    (h₃ : ∀ i j, B (f i) (e' j) = 0) (h₄ : ∀ i j, B (f i) (f' j) = 0) :
    IsSymplecticFamily B (Sum.elim e e') (Sum.elim f f') (Sum.elim d d') where
  left_left
    | .inl i, .inl j => h.left_left i j
    | .inl i, .inr j => h₁ i j
    | .inr i, .inl j => hB.eq_iff.1 (h₁ j i)
    | .inr i, .inr j => h'.left_left i j
  right_right
    | .inl i, .inl j => h.right_right i j
    | .inl i, .inr j => h₄ i j
    | .inr i, .inl j => hB.eq_iff.1 (h₄ j i)
    | .inr i, .inr j => h'.right_right i j
  left_right_self
    | .inl i => h.left_right_self i
    | .inr i => h'.left_right_self i
  left_right_ne
    | .inl i, .inl j, hij => h.left_right_ne i j fun a => hij (congrArg _ a)
    | .inl i, .inr j, _ => h₂ i j
    | .inr i, .inl j, _ => hB.eq_iff.1 (h₃ j i)
    | .inr i, .inr j, hij => h'.left_right_ne i j fun a => hij (congrArg _ a)
end GlobalTheory.IsSymplecticFamily
