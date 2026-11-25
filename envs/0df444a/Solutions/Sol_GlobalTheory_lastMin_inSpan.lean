-- Prove2me | solution 1 for GlobalTheory.lastMin_inSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:12.29591+00:00
-- url     : https://prove2.me/submissions/8e3a666d-869c-4529-869d-8860acafd7a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMin_inSpan

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
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) : lastMin (inSpan L) = lastMin L := by
  have h : span ℝ (inSpan L : Set (span ℝ (L : Set E))) = ⊤ := span_span_coe_preimage
  rw [lastMin, succMin_inSpan, h, finrank_top, lastMin]
end GlobalTheory
