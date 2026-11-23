-- Prove2me | solution 1 for KernelRank.singleCoeff_of_ne_idx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:10:40.308046+00:00
-- url     : https://prove2.me/submissions/10781547-dc86-47be-bf0d-c1810938d63b

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
theorem _root_.solution {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) {i : ι} (hi : i ≠ i₀) (q : Fin (m₀ i)) :
    singleCoeff i₀ q₀ z i q = 0 := by
  simp [singleCoeff, hi]
end KernelRank
