-- Prove2me | solution 1 for Hollom.no_spinalMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:23.293432+00:00
-- url     : https://prove2.me/submissions/94b4f535-cfc3-4c36-a7f8-b0bf8dfdc23c

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
import Theorems.Thm_Hollom_exists_finite_intersection
import Theorems.Thm_Hollom_S_mapsTo_previous
import Theorems.Thm_Hollom_not_S_mapsTo_previous

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (hC : IsChain (· ≤ ·) C) (f : SpinalMap C) : False := by
  obtain ⟨n, hn, hn'⟩ : ∃ n, n ≠ 0 ∧ (C ∩ Hollom.level n).Finite := by
    obtain ⟨n, hn, hn'⟩ := Filter.frequently_atTop.1 (Hollom.exists_finite_intersection hC) 1
    exact ⟨n, by omega, hn'⟩
  exact Hollom.not_S_mapsTo_previous hC hn' hn (Hollom.S_mapsTo_previous f hC hn)
end Hollom
