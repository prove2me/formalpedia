-- Prove2me | solution 1 for GlobalTheory.card_pow_eq_one_le_of_isCyclic_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:26.042821+00:00
-- url     : https://prove2.me/submissions/a1da7a34-2fdf-43c7-9355-009e251e2f15

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Theorems.Thm_GlobalTheory_card_pow_eq_one_le_units
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma card_pow_eq_one_le_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {n : ℕ}
    (hn : 0 < n) : Nat.card {a : α // a ^ n = 1} ≤ n := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsCyclic.card_pow_eq_one_le (α := α) hn
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] {d : ℕ}
    (hd : 0 < d) : Nat.card {x : ZMod n // x ^ d = 1} ≤ d :=
  (card_pow_eq_one_le_units hd).trans (card_pow_eq_one_le_of_isCyclic hd)
end GlobalTheory
