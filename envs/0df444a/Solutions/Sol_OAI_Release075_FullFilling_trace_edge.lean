-- Prove2me | solution 1 for OAI.Release075.FullFilling.trace_edge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:55:14.854893+00:00
-- url     : https://prove2.me/submissions/769a8a73-3d0a-42f4-9a3e-15454bb5682c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean:L330-L357
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.trace_edge. The node keeps its source
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

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Integral Stokes accounting for an antisymmetric edge evaluation. -/
theorem trace_edge {w : List E} (D : FullFilling flip color face w)
    (F : E → M) (hf : ∀ e, F (flip e) = -F e) :
    D.trace (fun a _ _ => F a) = -(w.map F).sum := by
  let f : D.Dart → M := F ∘ D.label
  have hz : ∑ a, f a = 0 := by
    apply Finset.sum_involution (fun a _ => D.reverse a)
    · intro a _
      simp only [f,Function.comp_apply,D.reverse_label,hf,add_neg_cancel]
    · intro a _ _; exact D.reverse_ne a
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact D.reverse_involutive a
  have hb : (∑ a, if a ∈ D.boundary then f a else 0) = (w.map F).sum := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun a => a ∈ D.boundary) = D.boundary.toFinset := by ext; simp
    rw [he,List.sum_toFinset _ D.boundary_cycle.1]
    change (D.boundary.map (F ∘ D.label)).sum = _
    rw [← List.map_map,D.boundary_word]
  have hpart : (∑ a, if a ∈ D.boundary then f a else 0) +
      D.trace (fun a _ _ => F a) = ∑ a, f a := by
    rw [trace,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp only [add_zero,zero_add,f,Function.comp_apply]
  rw [hb,hz] at hpart
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact hpart

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.trace_edge := @_root_.OAI.Release075.FullFilling.trace_edge
