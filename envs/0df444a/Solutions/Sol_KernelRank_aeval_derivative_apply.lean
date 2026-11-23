-- Prove2me | solution 1 for KernelRank.aeval_derivative_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:33:58.573343+00:00
-- url     : https://prove2.me/submissions/9984e0c5-a959-4358-8562-f5f9c4d74d60

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
theorem _root_.solution (q P : ℂ[X]) :
    aeval (derivative : Module.End ℂ ℂ[X]) q P =
      ∑ k : Fin (P.natDegree + 1),
        (q.coeff k * (k.val.factorial : ℂ)) • hasseDeriv k P := by
  let N := max (q.natDegree + 1) (P.natDegree + 1)
  have hpow (k : ℕ) :
      ((derivative : Module.End ℂ ℂ[X]) ^ k) P =
        (k.factorial : ℂ) • hasseDeriv k P := by
    rw [Module.End.pow_apply, ← factorial_smul_hasseDeriv]
    simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  rw [aeval_eq_sum_range'
    (show q.natDegree < N from lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)) derivative]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hpow, smul_smul]
  change ∑ k ∈ Finset.range N, (q.coeff k * (k.factorial : ℂ)) • hasseDeriv k P =
    ∑ k : Fin (P.natDegree + 1),
      (fun k : ℕ => (q.coeff k * (k.factorial : ℂ)) • hasseDeriv k P) k
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (q.coeff k * (k.factorial : ℂ)) • hasseDeriv k P) (P.natDegree + 1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.le_max_right ..))
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [hasseDeriv_eq_zero_of_lt_natDegree P k (by omega), smul_zero]
end KernelRank
