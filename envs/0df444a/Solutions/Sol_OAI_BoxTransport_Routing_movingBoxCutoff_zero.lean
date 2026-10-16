-- Prove2me | solution 1 for OAI.BoxTransport.Routing.movingBoxCutoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:29:28.645981+00:00
-- url     : https://prove2.me/submissions/f608499a-69a7-48ea-b1c8-b7b9336ef254

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Flow.lean:L256-L275
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.movingBoxCutoff_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

-- ---- from OAI.Analysis.BoxTransport.Flow ----
namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem movingBoxCutoff_zero {c r : ℝ → Space} {η : ℝ} (hη : 0 < η)
    {p : SpaceTime} (hp : p.2 ∉ openBox (c p.1) (r p.1) (2 * η)) :
    movingBoxCutoff c r η p = 0 := by
  classical
  simp only [openBox, Set.mem_ofPred_eq, not_forall, not_lt] at hp
  obtain ⟨j, hj⟩ := hp
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rcases le_or_gt (p.2 j - c p.1 j) 0 with hleft | hright
  · rw [abs_of_nonpos hleft] at hj
    have hz : Real.smoothTransition
        ((r p.1 j + 2 * η + (p.2 j - c p.1 j)) / η) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    rw [hz, zero_mul]
  · rw [abs_of_pos hright] at hj
    have hz : Real.smoothTransition
        ((r p.1 j + 2 * η - (p.2 j - c p.1 j)) / η) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    rw [hz, mul_zero]

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.movingBoxCutoff_zero := @_root_.OAI.BoxTransport.Routing.movingBoxCutoff_zero
