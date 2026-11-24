-- Prove2me | solution 1 for Hollom.mapsTo_Icc_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:43:52.66926+00:00
-- url     : https://prove2.me/submissions/97769b87-b5d6-4cb7-b31d-2423286b96b2

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
import Theorems.Thm_Hollom_embed_image_Icc
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_SpinalMap_mapsTo_Icc_self
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
theorem _root_.solution (hC : IsChain (· ≤ ·) C) {a b c d n : ℕ}
    (hab : h(a, b, n) ∈ C) (hcd : h(c, d, n) ∈ C) :
    Set.MapsTo f
      ((Icc (a, b) (c, d)).image (embed n))
      ((Icc (a, b) (c, d)).image (embed n)) := by
  simp only [coe_image, coe_Icc, embed_image_Icc]
  exact f.mapsTo_Icc_self hC hab hcd
end Hollom
