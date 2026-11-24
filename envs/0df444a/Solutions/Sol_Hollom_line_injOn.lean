-- Prove2me | solution 1 for Hollom.line_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:05.727897+00:00
-- url     : https://prove2.me/submissions/a806f3db-b67d-41fa-bb09-617724434e65

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
theorem _root_.solution {C : Set Hollom} (n : ℕ) (hC : IsChain (· ≤ ·) C) (hCn : C ⊆ level n) :
    C.InjOn line := by
  rw [Set.InjOn]
  intro x hx y hy h
  induction hCn hx using induction_on_level with | h a b =>
  induction hCn hy using induction_on_level with | h c d =>
  rcases hC.total hx hy with hxy | hxy
  · simp only [toHollom_le_toHollom_iff_fixed_right] at hxy
    simp only [line_toHollom] at h
    rcases hxy with ⟨h1, h2⟩
    have hac : a = c := by omega
    have hbd : b = d := by omega
    subst hac; subst hbd; rfl
  · simp only [toHollom_le_toHollom_iff_fixed_right] at hxy
    simp only [line_toHollom] at h
    rcases hxy with ⟨h1, h2⟩
    have hac : a = c := by omega
    have hbd : b = d := by omega
    subst hac; subst hbd; rfl
end Hollom
