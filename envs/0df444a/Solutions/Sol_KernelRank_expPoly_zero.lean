-- Prove2me | solution 1 for KernelRank.expPoly_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:26.054831+00:00
-- url     : https://prove2.me/submissions/247a8394-2df2-45fe-a6ad-6eeab0f658a4

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (μ : ℂ) (u : ℝ) : expPoly 0 μ u = 0 := by
  simp [expPoly]
end KernelRank
