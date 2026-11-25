-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.norm_tsum_eq_of_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:26.24207+00:00
-- url     : https://prove2.me/submissions/b3087a71-b501-4a01-88ff-f10bb4eb6725

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_norm_tsum_lt

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
theorem _root_.solution [CompleteSpace K] {ι : Type*} {f : ι → K}
    (hf : Tendsto f cofinite (𝓝 0)) (i₀ : ι) (h0 : f i₀ ≠ 0)
    (h : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  have hg : Tendsto (fun i => if i = i₀ then 0 else f i) cofinite (𝓝 0) := by
    refine hf.congr' ?_
    filter_upwards [(Set.finite_singleton i₀).compl_mem_cofinite] with i hi
    simp [show i ≠ i₀ from hi]
  have hsum : Summable (Function.update f i₀ 0) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (by convert hg using 1; funext i; simp [Function.update_apply])
  rw [hsum.tsum_eq_add_tsum_ite' i₀]
  have hlt : ‖∑' i, (if i = i₀ then 0 else f i)‖ < ‖f i₀‖ :=
    norm_tsum_lt hg (norm_pos_iff.2 h0) fun i => by
      by_cases hi : i = i₀
      · simp [hi, h0]
      · simpa [hi] using h i hi
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
end GroundTheory.PAdicHodge.Laurent
