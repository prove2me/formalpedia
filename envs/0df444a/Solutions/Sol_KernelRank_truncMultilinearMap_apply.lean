-- Prove2me | solution 1 for KernelRank.truncMultilinearMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:36:30.803878+00:00
-- url     : https://prove2.me/submissions/3e390c57-86bb-42f4-bd22-aabecbfae953

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero


attribute [local simp] KernelRank.singleCoeff_same

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) (u : Fin d → CoeffSpace m₀) :
    truncMultilinearMap d m₀ c w u = truncForm d m₀ c w u := by
  simp [truncMultilinearMap, truncForm, projCoeff]
end KernelRank
