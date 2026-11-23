-- Prove2me | solution 1 for KernelRank.separableRank_radial_lt_top_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:39.629072+00:00
-- url     : https://prove2.me/submissions/63304b8a-0d8b-4af3-8d3b-bbb228227481

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_radial_congr
import Theorems.Thm_KernelRank_exists_representation_of_finiteDimensional
import Theorems.Thm_KernelRank_separableRank_radial_profile_lt_top
import Theorems.Thm_KernelRank_separableRank_radial_two_le
import Theorems.Thm_KernelRank_separableRank_radial_two_lt_top_iff


set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) < ⊤ ↔
      ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by
  constructor
  · intro h
    have h2 : separableRank (fun x : Fin 2 → ℝ => φ (∑ j, x j ^ 2)) < ⊤ :=
      lt_of_le_of_lt (separableRank_radial_two_le hd φ) h
    have := (separableRank_radial_two_lt_top_iff φ).mp h2
    exact exists_representation_of_finiteDimensional φ hφ
  · rintro ⟨cs, _hcs, hφcs⟩
    rw [radial_congr hφcs]
    exact separableRank_radial_profile_lt_top hd cs
end KernelRank
