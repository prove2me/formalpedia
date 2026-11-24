-- Prove2me | solution 1 for Hollom.x0y0_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:14:11.608865+00:00
-- url     : https://prove2.me/submissions/1dfc623f-a0a5-4856-84b4-0d46584e759a

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
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_x0y0_mem
attribute [local ext] Hollom.SpinalMap.ext
attribute [local simp] Hollom.SpinalMap.toFun_eq_coe
attribute [local simp] Hollom.SpinalMap.mem
attribute [local simp] Hollom.SpinalMap.idempotent

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (z : ℕ × ℕ) (hC : IsChain (· ≤ ·) C) (h : embed (n + 1) z ∈ C) :
    embed (n + 1) (x0y0 n C) ≤ embed (n + 1) z := by
  have : (C ∩ level (n + 1)).Nonempty := ⟨_, h, by simp [level_eq_range]⟩
  rcases hC.total (x0y0_mem this) h with hle | hle
  · exact hle
  · rcases hle.eq_or_lt with heq | hlt
    · exact heq.ge
    · exfalso
      have hlt' : z < x0y0 n C := by rwa [← OrderEmbedding.lt_iff_lt (f := embed (n + 1))]
      rw [x0y0, dif_pos this] at hlt'
      exact wellFounded_lt.not_lt_min {x | embed (n + 1) x ∈ C} h hlt'
end Hollom
