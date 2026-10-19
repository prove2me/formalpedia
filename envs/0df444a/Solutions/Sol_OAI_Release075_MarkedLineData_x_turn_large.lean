-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.x_turn_large
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:15:19.776032+00:00
-- url     : https://prove2.me/submissions/16850b85-ea52-44fe-bf6f-dd27d8630072

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Links.lean:L114-L137
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.x_turn_large. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Theorems.Thm_OAI_Release075_MarkedLineData_incidences_girth
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

/-- The same girth bound controls a reduced path between distinct vertices of one
fiber of an immersion, even without a closing-seam condition. -/
theorem immersion_fiber_distance {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) (k : ℕ)
    (hgirth : ∀ a (w : H.Walk a a), w.IsCycle → k ≤ w.length)
    {a b : V} (hneq : a ≠ b) (heq : f a = f b) (p : G.Walk a b)
    (hp : ReducedWalk p) : k ≤ p.length := by
  have hpos : 0 < p.length := Nat.pos_iff_ne_zero.mpr (fun h => hneq (p.eq_of_length_eq_zero h))
  let w := (p.map f).copy rfl heq.symm
  have hr : ReducedWalk w := by
    intro n hn
    simpa only [w, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.getVert_copy] using
      (hp.map f hf n (by simpa only [w, SimpleGraph.Walk.length_copy] using hn))
  simpa [w] using reduced_closed_length_ge k hgirth w (by simpa [w] using hpos) hr

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

-- ---- from OAI.GroupTheory.Hyperbolic.Ribbons ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

attribute [instance] AngleDiskCounts.vertexFintype
namespace AngleDiskCounts
variable (D : AngleDiskCounts)

end AngleDiskCounts
end Release075

namespace Release075
open scoped BigOperators
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

attribute [instance] TriangleRibbon.dartFintype

namespace TriangleRibbon
variable (R : TriangleRibbon)
end TriangleRibbon
end Release075

namespace Release075.SumWalk
variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}

 theorem left_reduced {a b : U} {p : (G.sum H).Walk (.inl a) (.inl b)}
    (hp : ReducedWalk p) : ReducedWalk (left p) := by
  intro i hi heq
  apply hp i (by simpa only [left_length] using hi)
  have hh := congrArg (fun x : U => (Sum.inl x : U ⊕ V)) heq
  have hm (j : ℕ) : Sum.inl ((left p).getVert j) = p.getVert j := by
    have h := SimpleGraph.Walk.getVert_map (SimpleGraph.Embedding.sumInl (G := G) (H := H)).toHom (left p) j
    rw [map_left p] at h
    exact h.symm
  simpa only [hm] using hh

 theorem right_reduced {a b : V} {p : (G.sum H).Walk (.inr a) (.inr b)}
    (hp : ReducedWalk p) : ReducedWalk (right p) := by
  apply left_reduced
  exact hp.map _ (fun _ _ _ _ _ h => SimpleGraph.Iso.sumComm.injective h)

end Release075.SumWalk

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

end Release075.TriangleFilling

namespace Release075.SequenceWalk
variable {E : Type*} (L : SimpleGraph E)

end Release075.SequenceWalk

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

end Release075.TriangleRibbon

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Links ----
namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

 theorem v_reduced_same_label (i : d.Label) (u v u' v' : Fin r)
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk (.inr (.inl (.inl (i,u,v)))) (.inr (.inl (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 14 ≤ p.length := by
  let p' := SumWalk.left (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.left_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (d.vShift hr).projection
    (d.vShift hr).projection_locallyInjective 14 d.incidences_girth
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

 theorem w_reduced_same_label (i : d.Label) (u v u' v' : Fin r)
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk (.inr (.inr (.inl (i,u,v)))) (.inr (.inr (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 14 ≤ p.length := by
  let p' := SumWalk.right (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.right_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (d.wShift hr).projection
    (d.wShift hr).projection_locallyInjective 14 d.incidences_girth
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

 theorem x_turn_large (i : d.Label) (u v u' v' : Fin r) (s t : Bool)
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (.inl (i,u',v'),t)) =
      (d.presentation hr).edgeTarget (.inl (i,u,v),s))
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk
      (d.linkDirection hr ((d.presentation hr).flipEdge (.inl (i,u',v'),t)))
      (d.linkDirection hr (.inl (i,u,v),s)))
    (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (.inl (i,u,v),s))) * p.length := by
  cases s <;> cases t <;>
    simp only [BlockPresentation.flipEdge,BlockPresentation.edgeTarget,Bool.not_false,Bool.not_true] at ht
  · cases ht
  · have hh := d.v_reduced_same_label hr i u' v' u v hne.symm p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 14 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 14) hh)
  · have hh := d.w_reduced_same_label hr i v' u' v u
      (by simpa only [ne_eq,Prod.mk.injEq,and_comm] using hne.symm) p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 14 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 14) hh)
  · cases ht

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.x_turn_large := @_root_.OAI.Release075.MarkedLineData.x_turn_large
