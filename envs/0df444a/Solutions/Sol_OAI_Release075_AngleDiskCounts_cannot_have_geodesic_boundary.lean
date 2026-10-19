-- Prove2me | solution 1 for OAI.Release075.AngleDiskCounts.cannot_have_geodesic_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:05:27.959312+00:00
-- url     : https://prove2.me/submissions/0fedf211-6fdf-488e-8a34-1c5f7dc96194

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean:L41-L62
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.AngleDiskCounts.cannot_have_geodesic_boundary. The node keeps its source
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

/-- Gauss--Bonnet includes repeated boundary visits and naked edges. -/
theorem gauss_bonnet : ∑ v, D.curvature v = 10 := by
  have he : (Fintype.card D.Vertex : ℝ) + D.faces = D.edges + 1 := by exact_mod_cast D.euler
  have hb : (∑ v, (D.visits v : ℝ)) + 3*D.faces = 2*D.edges := by exact_mod_cast D.exterior
  simp only [curvature,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,← Finset.mul_sum]
  linarith [D.angle_sum]

/-- Curvature obstruction for a boundary all of whose cyclic turns have link
length >=π: an interior reduced link contributes >=2π and a single exterior
visit contributes >=π. Multiple visits require no turn estimate. -/
theorem cannot_have_geodesic_boundary
    (hinterior : ∀ v, D.visits v = 0 → 10 ≤ D.angles v)
    (hboundary : ∀ v, D.visits v = 1 → 5 ≤ D.angles v) : False := by
  have hnonpos (v : D.Vertex) : D.curvature v ≤ 0 := by
    by_cases h0 : D.visits v = 0
    · have h := hinterior v h0
      simp only [curvature,h0,Nat.cast_zero,mul_zero,sub_zero]
      linarith
    by_cases h1 : D.visits v = 1
    · have h := hboundary v h1
      simp only [curvature,h1,Nat.cast_one,mul_one]
      linarith
    · have h2 : (2 : ℝ) ≤ D.visits v := by exact_mod_cast (show 2 ≤ D.visits v by omega)
      have ha := D.angles_nonneg v
      dsimp [curvature]
      linarith
  have hs : (∑ v, D.curvature v) ≤ 0 := Finset.sum_nonpos (fun v _ => hnonpos v)
  rw [D.gauss_bonnet] at hs
  norm_num at hs

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


theorem solution : type_of% @_root_.OAI.Release075.AngleDiskCounts.cannot_have_geodesic_boundary := @_root_.OAI.Release075.AngleDiskCounts.cannot_have_geodesic_boundary
