-- Prove2me | solution 1 for KernelRank.differentialOperator_operatorOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:35:56.835619+00:00
-- url     : https://prove2.me/submissions/7b9ab43c-5191-4d94-b4f6-ea5cfeaa951d

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
import Theorems.Thm_KernelRank_iteratedDerivWithin_operatorOrbit
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Polynomial NNReal
open KernelRank
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] KernelRank._p2m_local_instance_4c459f894a_30
attribute [local instance] KernelRank._p2m_local_instance_4c459f894a_31
attribute [local instance] KernelRank._p2m_local_instance_4c459f894a_32
namespace KernelRank
theorem _root_.solution (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (p : ℂ[X]) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator p (operatorOrbit A v β) t =
      operatorOrbit A (aeval A p v) β t := by
  simp only [differentialOperator, iteratedDerivWithin_operatorOrbit A v β _ ht]
  simp [operatorOrbit, aeval_eq_sum_range, map_sum, map_smul, smul_eq_mul]
end KernelRank
