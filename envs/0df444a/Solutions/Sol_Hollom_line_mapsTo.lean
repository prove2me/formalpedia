-- Prove2me | solution 1 for Hollom.line_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:10.782858+00:00
-- url     : https://prove2.me/submissions/743f2a84-922a-41d1-b3ef-a2abe4e6c103

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
theorem _root_.solution {x y : Hollom} (hxy : (ofHollom x).2.2 = (ofHollom y).2.2) :
    Set.MapsTo line (Set.Icc x y) (Set.Icc (line x) (line y)) := by
  induction x with | h a b c =>
  induction y with | h d e f =>
  obtain rfl : c = f := by simpa using hxy
  rintro z ⟨h₁, h₂⟩
  induction z with | h p q r =>
  simp only [Set.mem_Icc, line_toHollom]
  obtain rfl := (le_of_toHollom_le_toHollom h₁).antisymm (le_of_toHollom_le_toHollom h₂)
  simp only [toHollom_le_toHollom_iff_fixed_right] at h₁ h₂
  omega
end Hollom
