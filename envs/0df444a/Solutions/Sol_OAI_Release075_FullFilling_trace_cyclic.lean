-- Prove2me | solution 1 for OAI.Release075.FullFilling.trace_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:53:32.488726+00:00
-- url     : https://prove2.me/submissions/67062ad2-8644-45e9-bfba-e0dab5ab76c1

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean:L264-L282
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.trace_cyclic. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing

-- ---- from OAI.GroupTheory.Hyperbolic.FullGluing ----
namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Cyclic reindexing of corners of genuine triangles. -/
theorem trace_cyclic {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) : D.trace (fun a b c => F b c a) = D.trace F := by
  let f : D.Dart → M := fun a => if a ∈ D.boundary then 0 else
    F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hsum := Equiv.sum_comp D.next f
  rw [trace]
  change _ = ∑ a, f a
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro a _
  have hm := D.boundary_cycle.mem_iff a
  by_cases ha : a ∈ D.boundary
  · simp only [f,ha,hm,ite_true]
  · have h3 : (D.next^2) (D.next a) = a := by
      simpa only [pow_succ,Perm.mul_apply] using ht a ha
    simp only [f,ha,hm,ite_false,h3]
    rw [pow_two,Perm.mul_apply]

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.trace_cyclic := @_root_.OAI.Release075.FullFilling.trace_cyclic
