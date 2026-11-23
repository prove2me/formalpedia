-- Prove2me | solution 1 for KernelRank.Component.multiCost_eq_borderCost_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:24:57.560873+00:00
-- url     : https://prove2.me/submissions/5ed73728-4434-4a78-937f-4fb325851577

import Mathlib
import Definitions.Def_KernelRankLean_Defs

set_option autoImplicit true
open Complex Polynomial
open KernelRank
open KernelRank.Component
namespace KernelRank.Component
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (c : Component) :
    c.multiCost d = c.borderCost d + (d - 2) * c.poly.natDegree := by
  unfold multiCost borderCost
  have hd1 : 1 ≤ d := by omega
  split_ifs <;> zify [hd, hd1] <;> ring
end KernelRank.Component
