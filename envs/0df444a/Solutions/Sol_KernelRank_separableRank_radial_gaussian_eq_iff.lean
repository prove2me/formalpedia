-- Prove2me | solution 1 for KernelRank.separableRank_radial_gaussian_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:53:52.485309+00:00
-- url     : https://prove2.me/submissions/e3b7d82a-a1db-466b-ac92-b6fa9551a79a

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_radial_congr
import Theorems.Thm_KernelRank_separableRank_radial_gaussian_profile


set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (φ : ℝ → ℝ)
    (hφ : ∃ cs : List Component, IsGaussianRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s)
    (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsGaussianRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ gaussianTotalCost d cs = N := by
  constructor
  · intro h
    obtain ⟨cs, hcs, hφcs⟩ := hφ
    refine ⟨cs, hcs, hφcs, ?_⟩
    rw [radial_congr hφcs, separableRank_radial_gaussian_profile hd hcs] at h
    exact_mod_cast h
  · rintro ⟨cs, hcs, hφcs, rfl⟩
    rw [radial_congr hφcs, separableRank_radial_gaussian_profile hd hcs]
end KernelRank
