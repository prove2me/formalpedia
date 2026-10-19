-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.incidences_girth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:39:10.47216+00:00
-- url     : https://prove2.me/submissions/f483beba-7ce7-42fd-b9fe-e124239c2b0d

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Presentation.lean:L520-L534
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.incidences_girth. The node keeps its source
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

/-- Bipartiteness gives four as the least possible cycle length, without a finiteness assumption. -/
theorem relationGraph_cycle_length {A B : Type*} (R : A → B → Prop)
    (a : A ⊕ B) (p : (relationGraph R).Walk a a) (hp : p.IsCycle) : 4 ≤ p.length := by
  let c : (relationGraph R).Coloring Bool :=
    {toFun := Sum.elim (fun _ => false) (fun _ => true)
     map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}
  have he := (c.even_length_iff_congr p).mpr Iff.rfl
  have ht := hp.three_le_length
  obtain ⟨n,hn⟩ := he
  omega

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

theorem incidences_girth (a : d.Label ⊕ (Fin 20 → ZMod q))
    (p : (relationGraph (fun i z => i ∈ d.incidences z)).Walk a a) (hp : p.IsCycle) :
    14 ≤ p.length := by
  have hi : Function.Injective d.swapIncidence := by
    intro x y h
    have hh := congrArg Sum.swap h
    simpa [swapIncidence] using hh
  have hh := d.girth _ (p.map d.swapIncidence) (hp.map hi)
  simp only [SimpleGraph.Walk.length_map] at hh
  have he := relationGraph_cycle_length (fun i z => i ∈ d.incidences z) a p hp
  let c : (relationGraph (fun i z => i ∈ d.incidences z)).Coloring Bool :=
    {toFun := Sum.elim (fun _ => false) (fun _ => true)
     map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}
  obtain ⟨n,hn⟩ := (c.even_length_iff_congr p).mpr Iff.rfl
  omega

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.incidences_girth := @_root_.OAI.Release075.MarkedLineData.incidences_girth
