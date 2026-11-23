-- Prove2me | solution 1 for KernelRank.linearIndependent_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:26:21.452949+00:00
-- url     : https://prove2.me/submissions/1c84a66e-e9c5-4252-a0ab-e085f7f801a1

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open KernelRank
namespace KernelRank
theorem _root_.solution {α ι : Type*} {f : ι → α → ℝ} (hf : LinearIndependent ℝ f) :
    LinearIndependent ℂ (fun i x => (f i x : ℂ)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hre : ∑ j ∈ s, (c j).re • f j = 0 := by
    ext x
    have := congrArg Complex.re (congrFun hc x)
    simpa [Finset.sum_apply, Complex.mul_re] using this
  have him : ∑ j ∈ s, (c j).im • f j = 0 := by
    ext x
    have := congrArg Complex.im (congrFun hc x)
    simpa [Finset.sum_apply, Complex.mul_im] using this
  exact Complex.ext ((linearIndependent_iff'.mp hf) s (fun j => (c j).re) hre i hi)
    ((linearIndependent_iff'.mp hf) s (fun j => (c j).im) him i hi)
end KernelRank
