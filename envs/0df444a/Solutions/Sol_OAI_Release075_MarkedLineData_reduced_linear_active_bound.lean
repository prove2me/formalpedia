-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.reduced_linear_active_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:19:16.453989+00:00
-- url     : https://prove2.me/submissions/d5e957b3-fbe6-41bc-b8da-eafb40660cc6

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Rectangles.lean:L124-L142
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.reduced_linear_active_bound. The node keeps its source
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
import Theorems.Thm_OAI_Release075_AngleDiskCounts_linear_face_bound
import Theorems.Thm_OAI_Release075_MarkedLineData_allLink_closed
import Theorems.Thm_OAI_Release075_TriangleFilling_dipole_of_link_backtrack
import Theorems.Thm_OAI_Release075_TriangleRibbon_interior_angle_lower

-- ---- from OAI.GroupTheory.Hyperbolic.Words ----
namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

namespace WordPath
variable {a b c : V} {u v : List E}

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))

end Fillable

namespace FilledBetween
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))
variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem TriangleFace.mirror {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace (d.flipEdge a) (d.flipEdge c) (d.flipEdge b) := by
  cases h with
  | pos₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v
  | pos₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₂ (d := d) b i u v
  | pos₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₁ (d := d) b i u v
  | neg₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₀ (d := d) b i u v
  | neg₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₂ (d := d) b i u v
  | neg₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₁ (d := d) b i u v

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem TriangleFace.unique_aux {a b c a' b' c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a' b' c')
    (ha : a = a') (hb : b = b') : c = c' := by
  cases h <;> cases h' <;>
    simp only [orientedL,orientedX,orientedR,flipEdge,Prod.mk.injEq,
      Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      Bool.not_true,and_true,false_and] at ha hb ⊢
  all_goals
    first
    | have hbb := congrArg Sigma.fst ha; cases hbb
    | have hbb := congrArg Sigma.fst hb; cases hbb
  all_goals simp only [Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,Subtype.val_inj,true_and] at ha hb ⊢
  case pos₀.pos₀ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case pos₁.pos₁ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp
  case pos₂.pos₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hβ⟩
    rcases hb with ⟨rfl,hα⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₀.neg₀ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hα⟩
    rcases hb with ⟨rfl,hβ⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₁.neg₁ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case neg₂.neg₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp

theorem TriangleFace.unique {a b c c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a b c') : c = c' :=
  TriangleFace.unique_aux d h h' rfl rfl

end Release075.BlockPresentation

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Dipoles ----
namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

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

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x hx hnx hnb h
  exact hD.false P

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

end CyclicLink
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Links ----
namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

 theorem linkDirection_color (a : (d.presentation hr).OrientedEdge) :
    d.linkColor hr (d.linkDirection hr a) =
      (d.presentation hr).vertexColor ((d.presentation hr).edgeTarget a) := by
  rcases a with ⟨a,s⟩
  rcases a with ⟨i,u,v⟩|l|s' <;> cases s <;> rfl

 theorem linkDirection_injective : Function.Injective (d.linkDirection hr) := by
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  rcases a with ⟨i,u,v⟩|l|s'
  all_goals rcases b with ⟨j,u',v'⟩|l'|t'
  all_goals cases s <;> cases t <;> simp_all [linkDirection]
  all_goals exact Sum.inr.inj h

 theorem face_corner_adj {a b c : (d.presentation hr).OrientedEdge}
    (h : (d.presentation hr).TriangleFace a b c) :
    (d.allLink hr).Adj (d.linkDirection hr a)
      (d.linkDirection hr ((d.presentation hr).flipEdge b)) := by
  cases h <;>
    simp only [BlockPresentation.orientedL,BlockPresentation.orientedX,
      BlockPresentation.orientedR,BlockPresentation.flipEdge, Bool.not_true,
      Bool.not_false, linkDirection,allLink,SimpleGraph.sum_adj_inl,SimpleGraph.sum_adj_inr]
  all_goals first | exact True.intro | exact ⟨Subtype.prop _,rfl,rfl⟩

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

theorem ribbon_outer_iff (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).IsOuter a ↔ a.val ∈ D.boundary :=
  D.active_boundary_iff hb a

theorem ribbon_color (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).color (cl (d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkColor hr (d.dartDirection hr D a) := by
  change (D.activeColor (d.presentation hr).vertexColor) (cl (D.activeReverse*D.activeNext) a) = _
  rw [TriangleFilling.activeColor,descend_cl]
  exact (d.linkDirection_color hr (D.label a)).symm

theorem ribbon_direction_step (a : D.ActiveDart) :
    d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkDirection hr ((d.presentation hr).flipEdge (D.label (D.next a))) := by
  change d.linkDirection hr (D.label (D.reverse (D.next a))) = _
  rw [D.reverse_label]

theorem ribbon_adj (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a) :
    (d.allLink hr).Adj (d.dartDirection hr D a)
      (d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  rw [d.ribbon_direction_step hr D b hb a]
  exact d.face_corner_adj hr (D.triangular a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))).2.2

theorem ribbon_reduced (hD : IsEmpty D.Dipole) (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a)
    (ha' : ¬(d.concreteRibbon hr D b hb).IsOuter ((d.concreteRibbon hr D b hb).vertexPerm a)) :
    d.dartDirection hr D a ≠
      d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm
        ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  intro he
  apply D.noDipole_link_reduced
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
    (d.presentation hr).flipEdge_flipEdge
    (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
    (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))
    (fun h => ha' ((d.ribbon_outer_iff hr D b hb _).mpr h))
  exact d.linkDirection_injective hr he

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Rectangles ----
namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

theorem ribbon_closed_strict (a : D.ActiveDart)
    (p : (d.allLink hr).Walk (d.dartDirection hr D a) (d.dartDirection hr D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight ((d.concreteRibbon hr D b hb).color
      (cl (d.concreteRibbon hr D b hb).vertexPerm a)) * p.length := by
  rw [d.ribbon_color hr D b hb a]
  exact d.allLink_closed hr _ p hn hp

theorem ribbon_boundary_length : (d.concreteRibbon hr D b hb).counts.boundaryLength = w.length := by
  let R := d.concreteRibbon hr D b hb
  change (∑ v : R.Vertex, R.visits v) = _
  rw [R.visits_sum]
  let e : {a : R.Dart // cl R.face a = R.outer} ≃ {a : D.Dart // a ∈ D.boundary} := {
    toFun a := ⟨a.val.val,(d.ribbon_outer_iff hr D b hb a.val).mp a.property⟩
    invFun a := ⟨⟨a.val,D.active_of_mem a.property⟩,
      (d.ribbon_outer_iff hr D b hb _).mpr a.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_subtype]
  have hset : Finset.univ.filter (fun a => a ∈ D.boundary) = D.boundary.toFinset := by
    ext a; simp
  rw [hset,List.toFinset_card_of_nodup D.boundary_cycle.1]
  exact (List.length_map D.label).symm.trans (congrArg List.length D.boundary_word)

include b hb in
theorem reduced_linear_active_bound (hD : IsEmpty D.Dipole) :
    D.activeCount + 36 ≤ 19*w.length := by
  let R := d.concreteRibbon hr D b hb
  have hstrict := R.interior_angle_lower (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD) 12
    (d.ribbon_closed_strict hr D b hb)
  have hface := R.counts.linear_face_bound hstrict
  have hlen := d.ribbon_boundary_length hr D b hb
  change R.counts.boundaryLength = w.length at hlen
  rw [hlen] at hface
  have hdart : Fintype.card R.Dart = D.activeCount := by
    change Fintype.card D.ActiveDart = _
    exact Fintype.card_subtype _
  have he := R.exterior_count
  rw [← R.dart_card,hdart] at he
  change R.counts.boundaryLength + 3*R.counts.faces = D.activeCount at he
  rw [hlen] at he
  omega

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.reduced_linear_active_bound := @_root_.OAI.Release075.MarkedLineData.reduced_linear_active_bound
