-- Prove2me | solution 1 for KernelRank.iteratedDerivWithin_sum_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:01.523935+00:00
-- url     : https://prove2.me/submissions/7862f1fe-989a-4be0-9f5a-d930a4c7a0bd

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_hasDerivAt_expPoly
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin k (fun u => ∑ i, expPoly (P i) (rate i) u) (Set.Ici 0) t =
      ∑ i, expPoly ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i)) (rate i) t := by
  induction k generalizing t with
  | zero => simp [iteratedDerivWithin_zero]
  | succ k ih =>
    rw [iteratedDerivWithin_succ]
    have heq : Set.EqOn
        (iteratedDerivWithin k (fun u => ∑ i, expPoly (P i) (rate i) u) (Set.Ici 0))
        (fun u => ∑ i, expPoly
          ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i)) (rate i) u)
        (Set.Ici 0) := fun u hu => ih hu
    rw [derivWithin_congr heq (heq ht),
      (HasDerivAt.fun_sum fun i _ => hasDerivAt_expPoly
        ((((derivative : Module.End ℂ ℂ[X]) + rate i • 1) ^ k) (P i))
        (rate i) t).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)]
    simp only [pow_succ', Module.End.mul_apply]
    simp [smul_eq_C_mul]
end KernelRank
