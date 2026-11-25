-- Prove2me | solution 1 for GlobalTheory.BadShare.primePowRoots_finite_ncard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:46.587395+00:00
-- url     : https://prove2.me/submissions/0f63fd46-83f5-4d15-b57b-796b727cc2ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
import Theorems.Thm_GlobalTheory_BadShare_pow_padicVal_eq_one_of_primePow

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
theorem _root_.solution (k : Type) [Field k] (n l : ℕ) (hn : 0 < n) (hl : l.Prime) :
    {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
      {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n := by
  have hm : 0 < l ^ padicValNat l n := pow_pos hl.pos _
  have hsub : {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} ⊆
      ((nthRoots (l ^ padicValNat l n) (1 : k)).toFinset : Set k) := by
    rintro y ⟨h1, a, h2⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hm]
    exact pow_padicVal_eq_one_of_primePow hn hl h1 h2
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)
end GlobalTheory.BadShare
