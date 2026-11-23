-- Prove2me | solution 1 for KernelRank.exists_ker_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:17:07.096801+00:00
-- url     : https://prove2.me/submissions/85013c42-09f5-4e64-92af-552ff9e34deb

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
theorem _root_.solution (L : ℂ →ₗ[ℝ] ℝ) : ∃ w : ℂ, w ≠ 0 ∧ L w = 0 := by
  by_cases h0 : L 1 = 0 ∧ L I = 0
  · exact ⟨1, one_ne_zero, h0.1⟩
  · refine ⟨(L I : ℂ) - (L 1 : ℂ) * I, ?_, ?_⟩
    · intro h
      have hre : L I = 0 := by simpa using congrArg Complex.re h
      have him : -L 1 = 0 := by simpa using congrArg Complex.im h
      exact h0 ⟨neg_eq_zero.mp him, hre⟩
    · have hw : ((L I : ℂ) - (L 1 : ℂ) * I) = (L I) • (1 : ℂ) - (L 1) • I := by
        simp [Complex.real_smul]
      rw [hw, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
end KernelRank
