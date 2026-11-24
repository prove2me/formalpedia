-- Prove2me | solution 1 for GlobalTheory.mem_succMinRadii_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:04.83093+00:00
-- url     : https://prove2.me/submissions/ba2b64b7-ac72-4bb8-9345-af5d8856289f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMinRadii_upper

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
theorem _root_.solution (hi : (i : Cardinal) ≤ Module.rank K (span K S))
    (h : succMinOf K N S i < r) : r ∈ succMinRadii K N S i := by
  obtain ⟨s, hs, hsr⟩ := exists_lt_of_csInf_lt (succMinRadii_nonempty_iff.2 hi) h
  exact succMinRadii_upper hs hsr.le
end GlobalTheory
