-- Prove2me | solution 1 for GlobalTheory.exists_mem_span_int_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:24.527781+00:00
-- url     : https://prove2.me/submissions/bf6fdece-bf53-46c2-a4bc-d5ec4de458af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_exists_mem_span_int_norm_sub_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (v : ι → E) {r : ℝ}
    (hr : ∀ i, ‖v i‖ ≤ r) {x : E} (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ≤ √(Fintype.card ι) / 2 * r := by
  obtain ⟨w, hw, h⟩ := exists_mem_span_int_norm_sub_sq_le v hx
  refine ⟨w, hw, ?_⟩
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have : ‖x - w‖ ^ 2 ≤ 0 := by simpa using h
    have h0 : ‖x - w‖ = 0 := by nlinarith [norm_nonneg (x - w)]
    simp [h0]
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr i₀)
  have hs : ∑ i, ‖v i‖ ^ 2 ≤ Fintype.card ι * r ^ 2 := by
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : ι, r ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hr i) 2
      _ = Fintype.card ι * r ^ 2 := by simp
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  linarith
end GlobalTheory
