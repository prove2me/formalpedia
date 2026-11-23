-- Prove2me | solution 1 for KernelRank.separableRank_radial_two_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:53:50.707856+00:00
-- url     : https://prove2.me/submissions/3ae07109-e922-41ee-8c0b-5ec561f92db6

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_separableRank_radial_eq_iff
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_multiTotalCost_two
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ totalCost cs = N := by
  simpa only [multiTotalCost_two] using separableRank_radial_eq_iff (le_refl 2) φ hφ N
end KernelRank
