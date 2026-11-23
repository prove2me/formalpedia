-- Prove2me | solution 1 for KernelRank.iteratedDerivWithin_operatorOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:33:54.538927+00:00
-- url     : https://prove2.me/submissions/261d7d95-3da5-4609-af31-cfffb6719af9

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
import Theorems.Thm_KernelRank_hasDerivAt_operatorOrbit
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
    (β : E →L[ℂ] ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin k (operatorOrbit A v β) (Set.Ici 0) t =
      operatorOrbit A ((A ^ k) v) β t := by
  induction k generalizing t with
  | zero => simp [iteratedDerivWithin_zero]
  | succ k ih =>
    rw [iteratedDerivWithin_succ]
    have heq : Set.EqOn
        (iteratedDerivWithin k (operatorOrbit A v β) (Set.Ici 0))
        (operatorOrbit A ((A ^ k) v) β) (Set.Ici 0) := fun u hu => ih hu
    rw [derivWithin_congr heq (heq ht),
      (hasDerivAt_operatorOrbit A ((A ^ k) v) β t).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici 0 t ht), pow_succ', mul_apply_eq_comp]
end KernelRank
