-- Prove2me | solution 1 for KernelRank.sum_shiftDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:18.88268+00:00
-- url     : https://prove2.me/submissions/9b38adf0-f556-48c7-894b-e2db36640501

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_expPoly_add
import Theorems.Thm_KernelRank_expPoly_C_mul
import Theorems.Thm_KernelRank_hasDerivAt_expPoly
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {S : Finset ℂ} {P : ℂ → ℂ[X]} (a : ℂ)
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) :
    ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (shiftDeriv a μ (P μ)) μ u = 0 := by
  intro u hu
  have hderiv : HasDerivAt (fun u => ∑ μ ∈ S, expPoly (P μ) μ u)
      (∑ μ ∈ S, expPoly (derivative (P μ) + C μ * P μ) μ u) u :=
    HasDerivAt.fun_sum fun μ _ => hasDerivAt_expPoly (P μ) μ u
  have hzero : HasDerivAt (fun u => ∑ μ ∈ S, expPoly (P μ) μ u) 0 u := by
    refine (hasDerivAt_const u (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hu] with v hv using h v hv
  have h0 : ∑ μ ∈ S, expPoly (derivative (P μ) + C μ * P μ) μ u = 0 := hderiv.unique hzero
  have h1 : ∑ μ ∈ S, expPoly (shiftDeriv a μ (P μ)) μ u =
      ∑ μ ∈ S, expPoly (derivative (P μ) + C μ * P μ) μ u -
        a * ∑ μ ∈ S, expPoly (P μ) μ u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : shiftDeriv a μ (P μ) = (derivative (P μ) + C μ * P μ) + C (-a) * P μ := by
      simp only [shiftDeriv, C_sub, C_neg]
      ring
    rw [this, expPoly_add, expPoly_C_mul]
    ring
  rw [h1, h0, h u hu, mul_zero, sub_zero]
end KernelRank
