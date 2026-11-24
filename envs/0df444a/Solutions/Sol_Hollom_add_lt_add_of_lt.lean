-- Prove2me | solution 1 for Hollom.add_lt_add_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:13.844223+00:00
-- url     : https://prove2.me/submissions/45ff866a-6cf0-41c7-abb9-40014c16bb02

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

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
namespace Hollom
theorem _root_.solution {a b c d n : ℕ} (h : h(a, b, n) < h(c, d, n)) : a + b < c + d := by
  change embed n (a, b) < embed n (c, d) at h
  rw [OrderEmbedding.lt_iff_lt, Prod.lt_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
end Hollom
