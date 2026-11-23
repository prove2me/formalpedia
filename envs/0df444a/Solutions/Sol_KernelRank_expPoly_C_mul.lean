-- Prove2me | solution 1 for KernelRank.expPoly_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:50.469094+00:00
-- url     : https://prove2.me/submissions/24b3de55-adb0-42c6-8990-af89ad6483a7

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (c : ℂ) (P : ℂ[X]) (μ : ℂ) (u : ℝ) :
    expPoly (C c * P) μ u = c * expPoly P μ u := by
  simp [expPoly, mul_assoc]
end KernelRank
