-- Prove2me | solution 1 for GlobalTheory.norm_iterate_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:34.661157+00:00
-- url     : https://prove2.me/submissions/6759fddc-2371-4544-af92-a2bf476c3a9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
omit [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ‖ε^[j] x‖ ≤ (5 / 8) ^ j * ‖x‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (5 / 8 : ℝ) ^ j * ‖x‖ ≤ ‖x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
    have h2 : ε^[j] x ∈ ball (0 : V) r := by
      rw [mem_ball_zero_iff] at hx ⊢
      linarith
    rw [Function.iterate_succ_apply', pow_succ]
    linarith [hc _ h2]
end GlobalTheory
