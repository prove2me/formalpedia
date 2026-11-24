-- Prove2me | solution 1 for GlobalTheory.SurjectiveOfKerSq.eq_of_le_sup_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:51.700097+00:00
-- url     : https://prove2.me/submissions/6e1b851f-a89a-4157-ad8d-a03dd9a0d49d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SurjectiveOfKerSq
namespace GlobalTheory.SurjectiveOfKerSq
theorem _root_.solution {B : Type} [CommRing B] (I K : Ideal B) (m : ℕ)
    (hnil : I ^ (m + 1) = ⊥) (h1 : K ≤ I) (h2 : I ≤ K ⊔ I ^ 2) : I = K := by
  have key : ∀ n : ℕ, I ≤ K ⊔ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine h2.trans (sup_le le_sup_left ?_)
      calc I ^ 2 = I * I := pow_two I
        _ ≤ I * (K ⊔ I ^ (n + 1)) := Ideal.mul_mono_right ih
        _ = I * K ⊔ I ^ (n + 1 + 1) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ K ⊔ I ^ (n + 1 + 1) := sup_le_sup_right Ideal.mul_le_right _
  have := key m
  rw [hnil, sup_bot_eq] at this
  exact le_antisymm this h1
end GlobalTheory.SurjectiveOfKerSq
