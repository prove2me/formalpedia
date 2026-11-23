-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.norm_tsum_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:13.515795+00:00
-- url     : https://prove2.me/submissions/57b2836d-638a-4796-96e6-bfb83e45cdd9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution {ι : Type*} {f : ι → K} (hf : Tendsto f cofinite (𝓝 0)) {M : ℝ}
    (hM : 0 < M) (h : ∀ i, ‖f i‖ < M) : ‖∑' i, f i‖ < M := by
  classical
  have hS : {i | M / 2 ≤ ‖f i‖}.Finite := by
    have := Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hf).eventually (gt_mem_nhds (half_pos hM)))
    simpa only [not_lt] using this
  set s := insert (M / 2) (hS.toFinset.image fun i => ‖f i‖)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hlt : s.max' hs < M := (Finset.max'_lt_iff s hs).2 fun y hy => by
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact h i
  refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg ?_ fun i => ?_) hlt
  · exact (by linarith : (0:ℝ) ≤ M / 2).trans (s.le_max' _ (Finset.mem_insert_self _ _))
  · by_cases hi : M / 2 ≤ ‖f i‖
    · exact s.le_max' _ (Finset.mem_insert_of_mem
        (Finset.mem_image.2 ⟨i, by simpa [Set.Finite.mem_toFinset] using hi, rfl⟩))
    · exact (not_le.1 hi).le.trans (s.le_max' _ (Finset.mem_insert_self _ _))
end GroundTheory.PAdicHodge.Laurent
