-- Prove2me | solution 1 for Hollom.embed_image_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:09:21.938062+00:00
-- url     : https://prove2.me/submissions/918c1000-f441-4c0e-ab53-18a213412af6

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
theorem _root_.solution {a b c d n : ℕ} :
    embed n '' Set.Icc (a, b) (c, d) = Set.Icc h(a, b, n) h(c, d, n) := by
  rw [OrderEmbedding.image_Icc, embed_apply, embed_apply]
  rw [← level_eq_range]
  exact ordConnected_level
end Hollom
