-- Prove2me | solution 1 for OAI.BoxTransport.Routing.coordinateRank_strict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:37:01.057195+00:00
-- url     : https://prove2.me/submissions/66777f9d-1488-414e-933f-3c511e51dba7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Motion.lean:L26-L38
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.coordinateRank_strict. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion

-- ---- from OAI.Analysis.BoxTransport.Motion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Separated five-stage motions and explicit affine time-one delivery. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem coordinateRank_strict {n : ℕ} {f : Fin n → ℚ} {i j : Fin n}
    (hij : centerKey f i < centerKey f j) : coordinateRank f i < coordinateRank f j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans hij
  · intro he
    have hi : i ∈ Finset.univ.filter (fun k => centerKey f k < centerKey f j) := by
      simp [hij]
    rw [← he] at hi
    simp at hi

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.coordinateRank_strict := @_root_.OAI.BoxTransport.Routing.coordinateRank_strict
