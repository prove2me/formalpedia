-- Prove2me | solution 1 for KernelRank.separableRank_radial_le_natDegree_of_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:56.573804+00:00
-- url     : https://prove2.me/submissions/c0b0e972-3443-4805-af6d-02863a320bcb

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_Annihilator
import Theorems.Thm_KernelRank_exists_minimal_differential_annihilator

set_option autoImplicit true
open Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)]
    (hφ : ContinuousOn φ (Set.Ici 0)) {q : ℂ[X]} (hq : q ≠ 0)
    (hann : ∀ t, 0 ≤ t → differentialOperator q (fun s => (φ s : ℂ)) t = 0) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) ≤ q.natDegree := by
  obtain ⟨p, _, hrank, hp⟩ := exists_minimal_differential_annihilator φ hφ
  rw [hrank]
  exact_mod_cast natDegree_le_of_dvd ((hp q).mp hann) hq
end KernelRank
