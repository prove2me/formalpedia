-- Prove2me | solution 1 for Hollom.toHollom_le_toHollom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:06.646256+00:00
-- url     : https://prove2.me/submissions/5acd4030-dbc2-4015-b9cc-644436ecfe44

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
theorem _root_.solution {a b c d e f : ℕ} (h : (a, b) ≤ (d, e)) (hcf : f ≤ c) :
    h(a, b, c) ≤ h(d, e, f) := by
  simp only [Prod.mk_le_mk] at h
  obtain rfl | rfl | hc : f = c ∨ f + 1 = c ∨ f + 2 ≤ c := by omega
  · simpa using h
  · exact .next_add (by omega)
  · exact .twice hc
end Hollom
