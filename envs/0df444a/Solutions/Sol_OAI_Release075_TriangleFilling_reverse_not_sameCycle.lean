-- Prove2me | solution 1 for OAI.Release075.TriangleFilling.reverse_not_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:01:30.588786+00:00
-- url     : https://prove2.me/submissions/61390bbc-b185-4c22-af99-c60927cdaac3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean:L164-L185
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleFilling.reverse_not_sameCycle. The node keeps its source
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

/-- A genuinely triangular face cannot use both orientations of one geometric
edge: its three differently colored vertices and the endpoint matching forbid it. -/
theorem reverse_not_sameCycle (a : D.Dart) (ha : D.Active a) (hna : a ∉ D.boundary)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by
  obtain ⟨hp,hn,hface⟩ := D.triangular a ha hna
  obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
  intro h
  have hm : D.reverse a ∈ orbit D.next a := (mem_orbit _ _ _).mpr h
  rw [orbit_eq_image D.next a (by omega : 0 < 3) hp] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  fin_cases i
  · exact D.reverse_ne a hi.symm
  · have h := D.color_next ((D.next^2) a)
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    simp only [Perm.mul_apply,h3,← hi] at h
    exact h12 h
  · have h := D.color_next (D.next a)
    have hr : D.reverse ((D.next^2) a) = a := by rw [hi,D.reverse_involutive]
    change color (D.label (D.reverse ((D.next^2) a))) = color (D.label (D.next a)) at h
    rw [hr] at h
    exact h01 h

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

end CyclicLink
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.TriangleFilling.reverse_not_sameCycle := @_root_.OAI.Release075.TriangleFilling.reverse_not_sameCycle
