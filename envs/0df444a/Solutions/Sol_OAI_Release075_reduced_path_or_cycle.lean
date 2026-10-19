-- Prove2me | solution 1 for OAI.Release075.reduced_path_or_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:33:29.259184+00:00
-- url     : https://prove2.me/submissions/0bb12893-39ea-47b7-8753-e83c8d461d97

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Presentation.lean:L32-L63
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.reduced_path_or_cycle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

-- ---- from OAI.GroupTheory.Hyperbolic.Presentation ----
namespace OAI

namespace Release075

theorem ReducedWalk.tail {V : Type*} {G : SimpleGraph V} {a b c : V}
    {e : G.Adj a b} {p : G.Walk b c} (h : ReducedWalk (p.cons e)) : ReducedWalk p := by
  intro n hn
  have hh := h (n + 1) (by simpa using Nat.add_le_add_right hn 1)
  simpa only [SimpleGraph.Walk.getVert_cons_succ, Nat.add_right_comm n 1 2] using hh

/-- A reduced walk which is not a simple path contains a cycle of no greater length.
In particular, a nonempty reduced *closed* walk need not be reduced at its seam. -/
theorem reduced_path_or_cycle {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ReducedWalk p) :
    p.IsPath ∨ ∃ (c : V) (w : G.Walk c c), w.IsCycle ∧ w.length ≤ p.length := by
  classical
  induction p with
  | nil => exact Or.inl SimpleGraph.Walk.IsPath.nil
  | @cons a b c e p ih =>
    rcases ih hp.tail with hpath | ⟨d,w,hw,hlen⟩
    · by_cases ha : a ∈ p.support
      · right
        let t := p.takeUntil a ha
        have ht : t.IsPath := hpath.takeUntil ha
        have hedge : s(a,b) ∉ t.edges := by
          intro he
          have he' : s(b,a) ∈ t.edges := by simpa only [Sym2.eq_swap] using he
          have hlen : t.length = 1 := ht.length_eq_one_of_mem_edges he'
          have hget : p.getVert 1 = a := by
            change (p.takeUntil a ha).length = 1 at hlen
            simpa only [hlen] using p.getVert_length_takeUntil ha
          have hp0 := hp 0 (by
            simp only [SimpleGraph.Walk.length_cons]
            have hh := p.length_takeUntil_le_length ha
            change t.length ≤ p.length at hh
            omega)
          apply hp0
          simpa only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_cons_succ] using hget.symm
        exact ⟨a,t.cons e,(SimpleGraph.Walk.cons_isCycle_iff _ _).mpr ⟨ht,hedge⟩,
          Nat.add_le_add_right (p.length_takeUntil_le_length ha) 1⟩
      · exact Or.inl ((SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hpath,ha⟩)
    · exact Or.inr ⟨d,w,hw,hlen.trans (by simp)⟩

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

end ShiftScheme

end Release075

namespace Release075

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

end BlockPresentation

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI
namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075


theorem solution : type_of% @_root_.OAI.Release075.reduced_path_or_cycle := @_root_.OAI.Release075.reduced_path_or_cycle
