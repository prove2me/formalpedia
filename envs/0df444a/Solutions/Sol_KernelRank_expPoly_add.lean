-- Prove2me | solution 1 for KernelRank.expPoly_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:35.300928+00:00
-- url     : https://prove2.me/submissions/edef0c75-2078-40ae-b6da-24ce6b12e21a

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (P Q : ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (P + Q) μ u = expPoly P μ u + expPoly Q μ u := by
  simp [expPoly, add_mul]
end KernelRank
