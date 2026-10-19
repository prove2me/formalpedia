-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.allLink_closed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:13:23.94879+00:00
-- url     : https://prove2.me/submissions/15b7d51f-fea4-4e5e-a261-bd2af9442662

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Links.lean:L55-L79
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.allLink_closed. The node keeps its source
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
import Theorems.Thm_OAI_Release075_ShiftScheme_link_cycle_length
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

theorem v_link_girth (hr : 0 < r) (a)
    (p : (d.vShift hr).link.Walk a a) (hp : p.IsCycle) : 14 ≤ p.length :=
  (d.vShift hr).link_cycle_length 14 d.incidences_girth a p hp

theorem w_link_girth (hr : 0 < r) (a)
    (p : (d.wShift hr).link.Walk a a) (hp : p.IsCycle) : 14 ≤ p.length :=
  (d.wShift hr).link_cycle_length 14 d.incidences_girth a p hp

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

 theorem allLink_closed (a : d.AllDirections hr) (p : (d.allLink hr).Walk a a)
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight (d.linkColor hr a) * p.length := by
  rcases a with a|a|a
  · let p' := SumWalk.left p
    have hlen : p'.length = p.length := SumWalk.left_length p
    have hg := reduced_closed_length_ge 4 (relationGraph_cycle_length _) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced hp)
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,Fin.zero_eta,ite_true]
    exact_mod_cast (by omega : 12 ≤ 3*p.length)
  · let p' := SumWalk.left (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 14 (d.v_link_girth hr) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (1 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)
  · let p' := SumWalk.right (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 14 (d.w_link_girth hr) p'
      (by rw [hlen]; exact hn) (SumWalk.right_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (2 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.allLink_closed := @_root_.OAI.Release075.MarkedLineData.allLink_closed
