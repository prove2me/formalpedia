-- Prove2me | solution 1 for GlobalTheory.exists_ball_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:20.121991+00:00
-- url     : https://prove2.me/submissions/1d7159b2-49bf-48f4-9d36-22dd1a8e24ed

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
variable [CompleteSpace V]
omit [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    ∃ r > 0, ∃ C ≥ 0, (∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖) ∧
      ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := h.exists_nonneg
  have h1 := (h.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)).bound (c := 1 / 8)
    (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hC.bound.and h1)
  refine ⟨r, hr, C, hC0, fun x hx => ?_, fun x hx => by simpa using (hball x hx).1⟩
  have h2 := (hball x hx).2
  have h3 : ‖(2 : ℂ)⁻¹ • x‖ = 1 / 2 * ‖x‖ := by simp [norm_smul]
  have h4 := norm_le_norm_sub_add (ε x) ((2 : ℂ)⁻¹ • x)
  linarith
end GlobalTheory
