-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.isPreconnected_ball_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:40:01.328103+00:00
-- url     : https://prove2.me/submissions/bae842ef-f78e-48fc-86ec-d53d2b431252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution (c p : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball c r \ {p}) := by
  set e := OpenPartialHomeomorph.univBall c r with he
  have hs : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have ht : e.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hinj : Function.Injective e := by
    rw [← injOn_univ, ← hs]; exact e.injOn
  have hc : (e ⁻¹' {p}).Countable := (countable_singleton p).preimage hinj
  have h1 := (hc.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected.image e
    (OpenPartialHomeomorph.continuous_univBall c r).continuousOn
  have h2 : e '' (e ⁻¹' {p})ᶜ = ball c r \ {p} := by
    rw [← preimage_compl, image_preimage_eq_inter_range, ← image_univ, ← hs,
      e.image_source_eq_target, ht, inter_comm]
    rfl
  rwa [h2] at h1
end GlobalTheory.Published.LogLine
