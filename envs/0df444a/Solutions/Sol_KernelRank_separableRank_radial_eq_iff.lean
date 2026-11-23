-- Prove2me | solution 1 for KernelRank.separableRank_radial_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:51:37.787399+00:00
-- url     : https://prove2.me/submissions/3c935b5e-76cf-4a90-a817-f9920558f501

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_radial_congr
import Theorems.Thm_KernelRank_separableRank_radial_lt_top_iff_exists
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_radial_profile
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ multiTotalCost d cs = N := by
  constructor
  · intro h
    obtain ⟨cs, hcs, hφcs⟩ :=
      (separableRank_radial_lt_top_iff_exists hd φ hφ).mp (by rw [h]; simp)
    refine ⟨cs, hcs, hφcs, ?_⟩
    rw [radial_congr hφcs, separableRank_radial_profile hd hcs] at h
    exact_mod_cast h
  · rintro ⟨cs, hcs, hφcs, rfl⟩
    rw [radial_congr hφcs, separableRank_radial_profile hd hcs]
end KernelRank
