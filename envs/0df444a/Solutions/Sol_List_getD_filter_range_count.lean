-- Prove2me | solution 1 for List.getD_filter_range_count
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:50:32.934733+00:00
-- url     : https://prove2.me/submissions/86a82f0c-3fde-4046-a132-de7a3c0fc3d8

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/































































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/


































/-- The list of the `j < n` with `q j` has `Nat.count q n` members. -/
theorem length_filter_range (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ((List.range n).filter fun j => decide (q j)).length = Nat.count q n := by
  rw [Nat.count, List.countP_eq_length_filter]

/-- In the increasing list of the `j < n` with `q j`, the member `i` has the number
`Nat.count q i`. -/
theorem getD_filter_range_count_sourceProof (q : ℕ → Prop) [DecidablePred q] (n : ℕ) {i : ℕ}
    (hi : i < n) (hq : q i) :
    ((List.range n).filter fun j => decide (q j)).getD (Nat.count q i) 0 = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [List.getD_append _ _ _ _ (by
        rw [List.length_filter_range]
        exact (Nat.count_lt_count_succ_iff.2 hq).trans_le (Nat.count_monotone q h))]
      exact ih h
    · rw [List.getD_append_right _ _ _ _ (List.length_filter_range q i).le,
        List.length_filter_range, Nat.sub_self]
      simp [hq]




















/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/



















/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end


theorem solution : ∀ (q : Nat → Prop) [inst : @DecidablePred.{1} Nat q] (n : Nat) {i : Nat},
  @LT.lt.{0} Nat instLTNat i n →
    q i →
      @Eq.{1} Nat
        (@List.getD.{0} Nat (@List.filter.{0} Nat (fun (j : Nat) => @Decidable.decide (q j) (inst j)) (List.range n))
          (@Nat.count q inst i) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        i := by
  exact @List.getD_filter_range_count_sourceProof

#print axioms solution
