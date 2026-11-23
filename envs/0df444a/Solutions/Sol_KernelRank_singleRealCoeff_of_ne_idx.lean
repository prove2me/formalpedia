-- Prove2me | solution 1 for KernelRank.singleRealCoeff_of_ne_idx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:17:55.846824+00:00
-- url     : https://prove2.me/submissions/edd63c4d-20f9-440c-853f-2d968c1d7f3b

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
theorem _root_.solution {ι : Type*} [DecidableEq ι] {m : ι → ℕ} {i : ι} (i₀ : ι)
    (q₀ : Fin (m i₀)) (a : ℝ) (hi : i ≠ i₀) (q : Fin (m i)) :
    singleRealCoeff i₀ q₀ a i q = 0 := by
  simp [singleRealCoeff, hi]
end KernelRank
