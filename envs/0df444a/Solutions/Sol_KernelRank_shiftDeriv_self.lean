-- Prove2me | solution 1 for KernelRank.shiftDeriv_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:24.454944+00:00
-- url     : https://prove2.me/submissions/3cab58aa-f1db-43e0-a769-70e049ac212e

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (a : ℂ) (P : ℂ[X]) : shiftDeriv a a P = derivative P := by
  simp [shiftDeriv]
end KernelRank
