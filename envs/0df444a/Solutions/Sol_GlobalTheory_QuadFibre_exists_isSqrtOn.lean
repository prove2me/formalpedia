-- Prove2me | solution 1 for GlobalTheory.QuadFibre.exists_isSqrtOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:03:06.076247+00:00
-- url     : https://prove2.me/submissions/6f950e51-893b-4713-9c0e-fa06a1ea7a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCompactOpenUnitsSubgroupContinuousSqrt
import Theorems.Thm_GlobalTheory_QuadFibre_exists_local_sqrt_near_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by
  classical
  obtain ⟨N, g, hN, h1, hg, hsq⟩ := exists_local_sqrt_near_one K h2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hN 1 h1
  set r : ℝ := min (ε / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.closedBall (1 : K) r ⊆ N :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hclopen : IsClopen (Metric.closedBall (1 : K) r) := ⟨Metric.isClosed_closedBall, hopen⟩
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  refine ⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen,
    isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩
  · intro a ha b hb
    have hna := hnorm a ha
    rw [mem_closedBall_iff_norm] at ha hb ⊢
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rwa [norm_mul, hna, one_mul]
  · intro a ha
    have hna := hnorm a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hna
    rw [mem_closedBall_iff_norm] at ha ⊢
    have : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by field_simp; ring
    rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]
  · refine continuous_piecewise ?_ ?_ continuousOn_const
    · simp [hclopen.frontier_eq]
    · rw [Metric.isClosed_closedBall.closure_eq]
      exact hg.mono hsub
  · intro a ha
    rw [Set.piecewise_eq_of_mem _ _ _ ha]
    exact hsq a (hsub ha)
end GlobalTheory.QuadFibre
