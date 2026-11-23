-- Prove2me | solution 1 for KernelRank.sum_comp_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:11:16.881802+00:00
-- url     : https://prove2.me/submissions/018317bd-d5a0-465f-a4fd-30bbf1a84502

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
theorem _root_.solution {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (g : ℕ → M) (c : ι → ℕ) (i₀ : ι) (v : ℕ) :
    (∑ i, g (Function.update c i₀ v i)) + g (c i₀) = (∑ i, g (c i)) + g v := by
  rw [← Finset.add_sum_erase Finset.univ (fun i => g (Function.update c i₀ v i))
      (Finset.mem_univ i₀),
    ← Finset.add_sum_erase Finset.univ (fun i => g (c i)) (Finset.mem_univ i₀)]
  have her : ∑ i ∈ Finset.univ.erase i₀, g (Function.update c i₀ v i) =
      ∑ i ∈ Finset.univ.erase i₀, g (c i) :=
    Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]
  rw [her, Function.update_self]
  abel
end KernelRank
