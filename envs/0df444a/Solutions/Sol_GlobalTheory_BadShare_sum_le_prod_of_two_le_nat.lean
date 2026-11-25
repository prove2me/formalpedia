-- Prove2me | solution 1 for GlobalTheory.BadShare.sum_le_prod_of_two_le_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:40.220166+00:00
-- url     : https://prove2.me/submissions/a45c5a13-cb95-4c39-a626-a42ec45c48ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumLeProdOfTwoLeNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have key : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ 2 ≤ ∏ i ∈ s, f i := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using h a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
      have h3 := h a (Finset.mem_cons_self _ _)
      constructor
      · have := Nat.add_le_mul h3 h2
        omega
      · nlinarith
  exact key.1
end GlobalTheory.BadShare
