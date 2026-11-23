-- Prove2me | solution 1 for KernelRank.hasDerivAt_operatorOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:32:17.852265+00:00
-- url     : https://prove2.me/submissions/08d82d22-208b-4f7c-a235-b90dd8c0710b

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
import Theorems.Thm_KernelRank_IsSumOfProducts_comp


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
    (β : E →L[ℂ] ℂ) (t : ℝ) :
    HasDerivAt (operatorOrbit A v β) (operatorOrbit A (A v) β t) t := by
  let L := (β.comp (ContinuousLinearMap.apply ℂ E v)).restrictScalars ℝ
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const A t)
end KernelRank
