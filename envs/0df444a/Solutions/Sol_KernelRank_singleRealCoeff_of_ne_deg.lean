-- Prove2me | solution 1 for KernelRank.singleRealCoeff_of_ne_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:18:45.406695+00:00
-- url     : https://prove2.me/submissions/27144371-fbd3-4cf5-95b7-d410bde873e1

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
theorem _root_.solution {ι : Type*} [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (q₀ q : Fin (m i₀)) (a : ℝ) (hq : q ≠ q₀) :
    singleRealCoeff i₀ q₀ a i₀ q = 0 := by
  simp [singleRealCoeff, hq]
end KernelRank
