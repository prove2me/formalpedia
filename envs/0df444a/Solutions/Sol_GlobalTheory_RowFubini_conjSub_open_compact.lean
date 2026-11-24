-- Prove2me | solution 1 for GlobalTheory.RowFubini.conjSub_open_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:14.057803+00:00
-- url     : https://prove2.me/submissions/db6821a2-7b4e-40f4-8682-7d3eae39485e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
import Theorems.Thm_GlobalTheory_RowFubini_mem_conjSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
namespace GlobalTheory.RowFubini
theorem _root_.solution (K : Subgroup X) (b : X) (hKo : IsOpen (K : Set X))
    (hKc : IsCompact (K : Set X)) :
    IsOpen (conjSub K b : Set X) ∧ IsCompact (conjSub K b : Set X) := by
  let h : X ≃ₜ X := (Homeomorph.mulLeft b⁻¹).trans (Homeomorph.mulRight b)
  have e : (conjSub K b : Set X) = h ⁻¹' (K : Set X) := by
    ext x; simp [h, mem_conjSub]
  rw [e]
  exact ⟨hKo.preimage h.continuous, h.isCompact_preimage.mpr hKc⟩
end GlobalTheory.RowFubini
