-- Prove2me | solution 1 for Hollom.image_chainBetween_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:11:33.739514+00:00
-- url     : https://prove2.me/submissions/ec9c8eed-2308-4b76-ad51-c88c69fca82f

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
import Theorems.Thm_Hollom_chainBetween_isChain
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
open Finset
namespace Hollom
theorem _root_.solution {a b c d n : ℕ} :
    IsChain (· ≤ ·) (((chainBetween a b c d).image (embed n)) : Set Hollom) := by
  rw [coe_image]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  rcases chainBetween_isChain hx hy (fun h => hne (congrArg _ h)) with h | h <;> simp [h]
end Hollom
