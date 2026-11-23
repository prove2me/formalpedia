-- Prove2me | solution 1 for KernelRank.singleCoeff_of_ne_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:11:11.584324+00:00
-- url     : https://prove2.me/submissions/d330b08b-f459-4b18-bf01-1da884b511a7

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
    (i₀ : ι) (q₀ q : Fin (m₀ i₀)) (z : ℂ) (hq : q ≠ q₀) :
    singleCoeff i₀ q₀ z i₀ q = 0 := by
  simp [singleCoeff, hq]
end KernelRank
