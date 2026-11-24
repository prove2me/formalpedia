-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.isPreconnected_offDivisor_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:20.697233+00:00
-- url     : https://prove2.me/submissions/f37a3d94-23d6-484b-ad7a-4af8e9e57ee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_Published_LogLine_isPreconnected_ball_diff

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
theorem _root_.solution (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (S : Finset (Fin n)) :
    IsPreconnected (offDivisor (ball c r) S) := by
  have : offDivisor (ball c r) S =
      Set.pi univ fun i => if i ∈ S then ball (c i) r \ {0} else ball (c i) r := by
    ext z
    simp only [offDivisor, ball_pi c hr, mem_setOf_eq, Set.mem_pi, mem_univ, true_imp_iff]
    constructor
    · rintro ⟨h1, h2⟩ i
      split_ifs with hi
      · exact ⟨h1 i, h2 i hi⟩
      · exact h1 i
    · intro h
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · have := h i
        split_ifs at this
        · exact this.1
        · exact this
      · have := h i
        rw [if_pos hi] at this
        exact this.2
  rw [this]
  refine isPreconnected_univ_pi fun i => ?_
  split_ifs
  · exact isPreconnected_ball_diff _ _ hr
  · exact (convex_ball _ _).isPreconnected
end GlobalTheory.Published.LogLine
