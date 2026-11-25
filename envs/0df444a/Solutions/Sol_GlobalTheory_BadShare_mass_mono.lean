-- Prove2me | solution 1 for GlobalTheory.BadShare.mass_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:04:59.913594+00:00
-- url     : https://prove2.me/submissions/ae9deead-1c44-46b9-9bde-c42d57683d88

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {N : ℕ} {A B : (ZMod g)[X] → Prop}
    (h : ∀ f ∈ _root_.GlobalTheory.BadShare.sqSet g N, A f → B f) :
    _root_.GlobalTheory.BadShare.mass g N A ≤ _root_.GlobalTheory.BadShare.mass g N B := by
  unfold _root_.GlobalTheory.BadShare.mass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, h f hf.1 hf.2⟩
  · intro f _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
