-- Prove2me | solution 1 for KernelRank.differentialOperator_sum_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:36:13.789426+00:00
-- url     : https://prove2.me/submissions/5b7cd22e-872d-41db-9be8-ead23ac55091

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_iteratedDerivWithin_sum_expPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι]
    (q : ℂ[X]) (P : ι → ℂ[X]) (rate : ι → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator q (fun u => ∑ i, expPoly (P i) (rate i) u) t =
      ∑ i, expPoly (aeval ((derivative : Module.End ℂ ℂ[X]) + rate i • 1) q (P i)) (rate i) t := by
  simp only [differentialOperator, iteratedDerivWithin_sum_expPoly P rate _ ht, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [aeval_eq_sum_range, expPoly, eval_finsetSum, Finset.sum_mul, smul_eq_C_mul, mul_assoc]
end KernelRank
