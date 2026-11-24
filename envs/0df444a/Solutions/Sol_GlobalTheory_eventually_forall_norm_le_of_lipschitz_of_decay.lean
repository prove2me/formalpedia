-- Prove2me | solution 1 for GlobalTheory.eventually_forall_norm_le_of_lipschitz_of_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:01.574315+00:00
-- url     : https://prove2.me/submissions/4c215889-c62f-4383-b2dc-e0c33b4088eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X V E : Type*} {l : Filter X}
    [NormedAddCommGroup V] [ProperSpace V] [NormedAddCommGroup E] {h : X → V → E}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0)) {C D : ℝ} (hC : 0 ≤ C)
    (hL : ∀ᶠ x in l, ∀ a b, ‖h x a - h x b‖ ≤ C * ‖a - b‖)
    (hD : ∀ᶠ x in l, ∀ v, ‖v‖ * ‖h x v‖ ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∀ v, ‖h x v‖ ≤ ε := by
  have hR1 : (1 : ℝ) ≤ max 1 (D / ε) := le_max_left _ _
  have hDR : D ≤ ε * max 1 (D / ε) := by
    calc D = ε * (D / ε) := by field_simp
      _ ≤ ε * max 1 (D / ε) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le
  have hη : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
  have hCη : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  obtain ⟨S, -, hSfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : V) (max 1 (D / ε))) hη
  have hS : ∀ᶠ x in l, ∀ s ∈ S, ‖h x s‖ < ε / 2 := by
    rw [hSfin.eventually_all]
    intro s _
    have hs := hp s
    rw [tendsto_zero_iff_norm_tendsto_zero] at hs
    exact hs.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hS, hL, hD] with x hxS hxL hxD v
  by_cases hv : ‖v‖ ≤ max 1 (D / ε)
  · have hvb : v ∈ Metric.closedBall (0 : V) (max 1 (D / ε)) := by rwa [mem_closedBall_zero_iff]
    obtain ⟨s, hs, hvs⟩ := Set.mem_iUnion₂.1 (hcover hvb)
    rw [Metric.mem_ball, dist_eq_norm] at hvs
    have e : h x v = h x s + (h x v - h x s) := by abel
    calc ‖h x v‖ = ‖h x s + (h x v - h x s)‖ := by rw [← e]
      _ ≤ ‖h x s‖ + ‖h x v - h x s‖ := norm_add_le _ _
      _ ≤ ε / 2 + C * (ε / (2 * (C + 1))) :=
          add_le_add (hxS s hs).le ((hxL v s).trans (mul_le_mul_of_nonneg_left hvs.le hC))
      _ ≤ ε := by linarith
  · replace hv := not_le.1 hv
    have hvpos : 0 < ‖v‖ := lt_of_lt_of_le one_pos (hR1.trans hv.le)
    have hmul : ‖v‖ * ‖h x v‖ ≤ ‖v‖ * ε := by
      calc ‖v‖ * ‖h x v‖ ≤ D := hxD v
        _ ≤ ε * max 1 (D / ε) := hDR
        _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left hv.le hε.le
        _ = ‖v‖ * ε := mul_comm _ _
    exact le_of_mul_le_mul_left hmul hvpos
end GlobalTheory
