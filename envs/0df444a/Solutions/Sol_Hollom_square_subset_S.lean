-- Prove2me | solution 1 for Hollom.square_subset_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:27:19.595339+00:00
-- url     : https://prove2.me/submissions/ef7e3869-8b30-44a7-b80c-43315aa2f374

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
import Theorems.Thm_Hollom_square_subset_S_case_1
import Theorems.Thm_Hollom_square_subset_S_case_2

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) :=
  (C ∩ level (n + 1)).finite_or_infinite.elim (square_subset_S_case_1 h) (square_subset_S_case_2 h)
end Hollom
