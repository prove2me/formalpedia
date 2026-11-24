-- Prove2me | solution 1 for Hollom.not_R_hits_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:16:16.857259+00:00
-- url     : https://prove2.me/submissions/5fe58f6b-4610-4e6e-91e7-e8357ba18fbb

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
import Theorems.Thm_Hollom_SpinalMap_incomp_apply

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution {x : Hollom} (hx : x ∈ R n C) (hx' : x ∉ C ∩ level n) :
    f x ∉ C ∩ level n := by
  intro hfx
  apply f.incomp_apply _ (hx.2 _ hfx).symm
  exact ne_of_mem_of_not_mem hfx hx'
end Hollom
