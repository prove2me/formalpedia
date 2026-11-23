-- Prove2me | solution 1 for KernelRank.hasDerivAt_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:57:09.447147+00:00
-- url     : https://prove2.me/submissions/58c28e4c-98c1-483a-8a6d-a30fd67437e2

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (P : ℂ[X]) (μ : ℂ) (u : ℝ) :
    HasDerivAt (expPoly P μ) (expPoly (derivative P + C μ * P) μ u) u := by
  have h1 : HasDerivAt (fun u : ℝ => P.eval (u : ℂ)) ((derivative P).eval (u : ℂ)) u :=
    (P.hasDerivAt (u : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun u : ℝ => exp (μ * u)) (exp (μ * u) * μ) u := by
    have : HasDerivAt (fun u : ℝ => μ * (u : ℂ)) μ u := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_mul μ).comp_ofReal
    exact this.cexp
  refine (h1.mul h2).congr_deriv ?_
  simp only [expPoly, eval_add, eval_mul, eval_C]
  ring
end KernelRank
