-- Prove2me | solution 1 for GlobalTheory.BadShare.sum_le_prod_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:12.373454+00:00
-- url     : https://prove2.me/submissions/11fc7bbb-fce0-4697-bb13-b75fd336179f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha2 := h a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · simp
    · have hne : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => by
        have := h i (Finset.mem_insert_of_mem hi)
        omega
      have hP : 2 ≤ ∏ i ∈ s, f i :=
        (h b (Finset.mem_insert_of_mem hb)).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Finset.dvd_prod_of_mem f hb))
      nlinarith
end GlobalTheory.BadShare
