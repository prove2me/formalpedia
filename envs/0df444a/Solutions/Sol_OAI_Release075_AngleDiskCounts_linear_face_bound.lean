-- Prove2me | solution 1 for OAI.Release075.AngleDiskCounts.linear_face_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:07:14.102721+00:00
-- url     : https://prove2.me/submissions/69af42ac-e4b5-4333-a9dc-6867a017e452

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean:L99-L116
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.AngleDiskCounts.linear_face_bound. The node keeps its source
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

-- ---- from OAI.GroupTheory.Hyperbolic.Ribbons ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

attribute [instance] AngleDiskCounts.vertexFintype
namespace AngleDiskCounts
variable (D : AngleDiskCounts)

theorem vertices_partition : D.interior.card + D.boundary.card = Fintype.card D.Vertex := by
  classical
  simpa only [interior,boundary,Finset.card_univ] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => D.visits v = 0)

theorem boundary_card_le_length : D.boundary.card ≤ D.boundaryLength := by
  classical
  calc
    D.boundary.card = ∑ v ∈ D.boundary, 1 := by simp
    _ ≤ ∑ v ∈ D.boundary, D.visits v := by
      apply Finset.sum_le_sum
      intro v hv
      have h : D.visits v ≠ 0 := (Finset.mem_filter.mp hv).2
      omega
    _ ≤ D.boundaryLength := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The Euler/incidence formula in terms of interior and boundary vertices. -/
theorem face_vertex_formula :
    D.faces + D.boundaryLength + 2 = 2*D.interior.card + 2*D.boundary.card := by
  have he := D.euler
  have hb := D.exterior
  have hp := D.vertices_partition
  change D.boundaryLength + 3*D.faces = 2*D.edges at hb
  omega

theorem linear_face_bound
    (hinterior : ∀ v, D.visits v = 0 → 12 ≤ D.angles v) :
    D.faces + 12 ≤ 6*D.boundaryLength := by
  classical
  have ha : (12 : ℝ)*D.interior.card ≤ 5*D.faces := by
    calc
      (12 : ℝ)*D.interior.card = ∑ _v ∈ D.interior, (12 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ D.interior, D.angles v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hinterior v (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, D.angles v := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun v _ _ => D.angles_nonneg v)
      _ = 5*D.faces := D.angle_sum
  have ha' : 12*D.interior.card ≤ 5*D.faces := by exact_mod_cast ha
  have hp := D.face_vertex_formula
  have hb := D.boundary_card_le_length
  omega

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

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.AngleDiskCounts
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.AngleDiskCounts.linear_face_bound := @_root_.OAI.Release075.AngleDiskCounts.linear_face_bound
