-- Prove2me | solution 1 for OAI.Release075.ShiftScheme.link_cycle_length
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:36:20.78899+00:00
-- url     : https://prove2.me/submissions/ffcf462b-232c-4ff4-8b5c-7a0785f9cc30

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Presentation.lean:L203-L223
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.ShiftScheme.link_cycle_length. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Theorems.Thm_OAI_Release075_ShiftScheme_projection_locallyInjective
import Theorems.Thm_OAI_Release075_reduced_path_or_cycle

-- ---- from OAI.GroupTheory.Hyperbolic.Presentation ----
namespace OAI

namespace Release075

theorem ReducedWalk.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) {a b : V} {p : G.Walk a b}
    (hp : ReducedWalk p) : ReducedWalk (p.map f) := by
  intro n hn heq
  simp only [SimpleGraph.Walk.length_map] at hn
  simp only [SimpleGraph.Walk.getVert_map] at heq
  apply hp n hn
  apply hf (p.getVert (n+1)) _ _
    (p.adj_getVert_succ (by omega)).symm (p.adj_getVert_succ (by omega)) heq

theorem reduced_closed_length_ge {V : Type*} {G : SimpleGraph V} (k : ℕ)
    (hgirth : ∀ a (w : G.Walk a a), w.IsCycle → k ≤ w.length)
    {a : V} (p : G.Walk a a) (hne : 0 < p.length) (hp : ReducedWalk p) :
    k ≤ p.length := by
  rcases reduced_path_or_cycle p hp with hpath | ⟨c,w,hw,hlen⟩
  · have h := SimpleGraph.Walk.length_eq_zero_iff.mpr (SimpleGraph.Walk.isPath_iff_nil.mp hpath)
    omega
  · exact (hgirth c w hw).trans hlen

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

/-- Girth transfers through the locally injective projection. -/
theorem link_cycle_length (k : ℕ)
    (hgirth : ∀ a (w : (relationGraph (fun i z => i ∈ inc z)).Walk a a),
      w.IsCycle → k ≤ w.length)
    (a : XDirection (I := I) (r := r) ⊕ d.LDirection)
    (p : d.link.Walk a a) (hp : p.IsCycle) : k ≤ p.length := by
  have hred : ReducedWalk p := by
    intro n hn he
    have h3 := hp.three_le_length
    by_cases hn0 : n = 0
    · subst n
      have he' : p.getVert p.length = p.getVert 2 := by simpa using he
      have hh := hp.getVert_injOn (by exact ⟨by omega, le_rfl⟩)
        (by exact ⟨by omega, by omega⟩) he'
      omega
    · have hh := hp.getVert_injOn (by exact ⟨by omega, by omega⟩)
        (by exact ⟨by omega, hn⟩) he
      omega
  have hmap := hred.map d.projection d.projection_locallyInjective
  simpa using reduced_closed_length_ge k hgirth (p.map d.projection)
    (by have h3 := hp.three_le_length; simp only [SimpleGraph.Walk.length_map]; omega) hmap

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
open OAI OAI.Release075 OAI.Release075.ShiftScheme


theorem solution : type_of% @_root_.OAI.Release075.ShiftScheme.link_cycle_length := @_root_.OAI.Release075.ShiftScheme.link_cycle_length
