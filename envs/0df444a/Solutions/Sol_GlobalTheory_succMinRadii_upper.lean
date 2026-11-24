-- Prove2me | solution 1 for GlobalTheory.succMinRadii_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:35.941032+00:00
-- url     : https://prove2.me/submissions/4fa80f0e-9c23-41d8-aecf-cda8221c53ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

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
variable (K : Type*) [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {K}
variable {N N' : V → ℝ} {S S' : Set V} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution {r' : ℝ} (h : r ∈ succMinRadii K N S i) (hr : r ≤ r') :
    r' ∈ succMinRadii K N S i := by
  rw [mem_succMinRadii_iff] at h ⊢
  obtain ⟨h0, v, hv, hS⟩ := h
  exact ⟨h0.trans hr, v, hv, fun j => ⟨(hS j).1, (hS j).2.trans hr⟩⟩
end GlobalTheory
