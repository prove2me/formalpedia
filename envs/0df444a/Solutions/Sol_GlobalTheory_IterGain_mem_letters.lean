-- Prove2me | solution 1 for GlobalTheory.IterGain.mem_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:37.992778+00:00
-- url     : https://prove2.me/submissions/5c9e4374-2d66-4289-b837-92f44fd1c487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.IterGain
namespace GlobalTheory.IterGain
theorem _root_.solution {ι : Type} [DecidableEq ι] (B : Finset ι) :
    ∀ (k : ℕ), ∀ l ∈ words B k, ∀ i ∈ l, i ∈ B := by
  intro k
  induction k with
  | zero => intro l hl i hi; simp [words] at hl; subst hl; simp at hi
  | succ k ih =>
    intro l hl i hi
    simp only [words, mem_insert, mem_image, mem_product, Prod.exists] at hl
    rcases hl with rfl | ⟨l', j, ⟨hl', hj⟩, rfl⟩
    · simp at hi
    · rcases List.mem_append.1 hi with h | h
      · exact ih l' hl' i h
      · simp at h; subst h; exact hj
end GlobalTheory.IterGain
