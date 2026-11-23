-- Prove2me | solution 1 for KernelRank.realExpMultilinearMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:48.552141+00:00
-- url     : https://prove2.me/submissions/b51a8084-ed05-4777-be6a-13b4a46ecee7

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ)
    (u : Fin d → RealExpSpace m_R m_C) :
    realExpMultilinearMap d m_R m_C c_R c_C w_R w_C u =
      realExpForm d m_R m_C c_R c_C w_R w_C u := by
  simp [realExpMultilinearMap, realExpForm, realTruncForm, cplxTruncForm,
    projRealExp, projCplxExp]
end KernelRank
