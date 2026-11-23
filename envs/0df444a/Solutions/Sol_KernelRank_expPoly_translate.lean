-- Prove2me | solution 1 for KernelRank.expPoly_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:32:19.415913+00:00
-- url     : https://prove2.me/submissions/174a657f-5f81-446d-b6da-9e527d1e30fb

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
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
theorem _root_.solution {P : ℂ[X]} {m : ℕ} (hm : P.natDegree < m) (μ : ℂ) (u t : ℝ) :
    expPoly P μ (u + t) =
      ∑ k : Fin m, expPoly (X ^ (k : ℕ)) μ u * expPoly (hasseDeriv k P) μ t := by
  have htaylor : P.eval ((u : ℂ) + t) =
      ∑ k : Fin m, (hasseDeriv k P).eval (t : ℂ) * (u : ℂ) ^ (k : ℕ) := by
    rw [← taylor_eval, eval_eq_sum_range' (by rwa [natDegree_taylor]),
      ← Fin.sum_univ_eq_sum_range]
    simp [taylor_coeff]
  simp only [expPoly, Complex.ofReal_add, htaylor, eval_pow, eval_X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, Complex.exp_add]
  ring
end KernelRank
