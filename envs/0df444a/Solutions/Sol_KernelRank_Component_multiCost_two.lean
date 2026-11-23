-- Prove2me | solution 1 for KernelRank.Component.multiCost_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:24:52.781792+00:00
-- url     : https://prove2.me/submissions/39697e92-240e-4cad-befc-4c440ee133ea

import Mathlib
import Definitions.Def_KernelRankLean_Defs

set_option autoImplicit true
open Complex Polynomial
open KernelRank
open KernelRank.Component
namespace KernelRank.Component
theorem _root_.solution (c : Component) : c.multiCost 2 = c.cost := by
  unfold multiCost cost multiplicity
  split_ifs <;> omega
end KernelRank.Component
