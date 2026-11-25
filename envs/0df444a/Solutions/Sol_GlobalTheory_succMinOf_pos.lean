-- Prove2me | solution 1 for GlobalTheory.succMinOf_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:52.06624+00:00
-- url     : https://prove2.me/submissions/c5e90af5-223e-43ea-bc17-97f6893796b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMinOf_mem

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
theorem _root_.solution (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, x ≠ 0 → 0 < N x) (h1 : 1 ≤ i)
    (hi : (i : Cardinal) ≤ Module.rank K (span K S)) : 0 < succMinOf K N S i := by
  obtain ⟨-, v, hv, hS⟩ := mem_succMinRadii_iff.1 (succMinOf_mem hfin hi)
  exact (hN _ (hS ⟨0, h1⟩).1 (hv.ne_zero _)).trans_le (hS ⟨0, h1⟩).2
end GlobalTheory
