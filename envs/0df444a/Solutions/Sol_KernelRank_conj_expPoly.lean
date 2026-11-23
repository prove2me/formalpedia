-- Prove2me | solution 1 for KernelRank.conj_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:31:53.402171+00:00
-- url     : https://prove2.me/submissions/38596f96-af63-43cf-95a7-4ad6254644b8

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
import Theorems.Thm_KernelRank_eval_ofReal_conjPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero



set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (A : ℂ[X]) (μ : ℂ) (u : ℝ) :
    starRingEnd ℂ (expPoly A μ u) = expPoly (conjPoly A) (starRingEnd ℂ μ) u := by
  simp [expPoly, eval_ofReal_conjPoly, ← Complex.exp_conj, map_mul]
end KernelRank
