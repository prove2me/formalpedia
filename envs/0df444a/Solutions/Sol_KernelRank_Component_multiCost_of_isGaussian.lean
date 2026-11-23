-- Prove2me | solution 1 for KernelRank.Component.multiCost_of_isGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:24:54.627896+00:00
-- url     : https://prove2.me/submissions/08ff8a74-a25f-48df-a3b1-fb7605ad008c

import Mathlib
import Definitions.Def_KernelRankLean_Defs

set_option autoImplicit true
open Complex Polynomial
open KernelRank
open KernelRank.Component
namespace KernelRank.Component
theorem _root_.solution (d : ℕ) {c : Component} (hg : c.IsGaussian) :
    c.multiCost d = c.gaussianCost d := by
  unfold IsGaussian at hg
  simp [multiCost, gaussianCost, hg]
end KernelRank.Component
