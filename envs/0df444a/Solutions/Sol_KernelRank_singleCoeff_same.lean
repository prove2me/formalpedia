-- Prove2me | solution 1 for KernelRank.singleCoeff_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:08:26.944367+00:00
-- url     : https://prove2.me/submissions/12cab9e3-caad-4e32-9a73-ac0d7f89c711

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
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
theorem _root_.solution {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) :
    singleCoeff i₀ q₀ z i₀ q₀ = z := by
  simp [singleCoeff]
end KernelRank
