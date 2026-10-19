-- Prove2me | solution 1 for OAI.Release075.TriangleSphere.dipole_of_link_backtrack
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:24:55.610887+00:00
-- url     : https://prove2.me/submissions/dc4e3dae-f5bc-40a4-8c5b-f80522534fab

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Spheres.lean:L62-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleSphere.dipole_of_link_backtrack. The node keeps its source
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

 theorem trianglePairEmbedding_values (f : Perm A) (a b : A)
    (hpa : (f^3) a = a) (hna : f a ≠ a) (hpb : (f^3) b = b) (hnb : f b ≠ b)
    (hab : ¬ f.SameCycle a b) :
    let e := trianglePairEmbedding f a b hpa hna hpb hnb hab
    e 0 = a ∧ e 1 = f a ∧ e 2 = (f^2) a ∧
    e 3 = b ∧ e 4 = f b ∧ e 5 = (f^2) b := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

end CyclicLink
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Spheres ----
namespace OAI

namespace Release075
open Equiv PermCycles

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

theorem reverse_not_sameCycle (a : D.Dart)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by
  obtain ⟨hp,hn,hface⟩ := D.triangular a
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

/-- Internal reversal of a link walk creates a cancellable pair, when the face
labels are determined by two consecutive sides. -/
theorem dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by
  let a := D.next x
  let b := D.reverse a
  obtain ⟨hp,hne,hfa⟩ := D.triangular a
  obtain ⟨hp',hne',hfb⟩ := D.triangular b
  have hx3 := (D.triangular x).1
  have hax : (D.next^2) a = x := by
    change (D.next^2) (D.next x) = x
    simpa only [pow_succ,Perm.mul_apply] using hx3
  have h42 : D.label (D.next b) = flip (D.label ((D.next^2) a)) := by
    have he : D.label x = flip (D.label (D.next b)) := hback.trans (D.reverse_label (D.next b))
    rw [hax,he,hflip]
  have h51 : D.label ((D.next^2) b) = flip (D.label (D.next a)) := by
    apply hunique (D.label b) (D.label (D.next b)) _ _ hfb
    rw [h42]
    change face (D.label (D.reverse a)) (flip (D.label ((D.next^2) a))) (flip (D.label (D.next a)))
    rw [D.reverse_label]
    exact hmirror _ _ _ hfa
  have hab : ¬ D.next.SameCycle a b := D.reverse_not_sameCycle a hf
  let e := trianglePairEmbedding D.next a b hp hne hp' hne' hab
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := trianglePairEmbedding_values D.next a b hp hne hp' hne' hab
  have hnext : ∀ j, D.next (e j) = e (dipoleFace j) := by
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    have h3' : D.next ((D.next^2) b) = b := by simpa only [pow_succ',Perm.mul_apply] using hp'
    intro j
    fin_cases j <;> first | rfl | exact h3 | exact h3'
  obtain ⟨h01,h12,_⟩ := hf _ _ _ hfa
  refine ⟨{
    dart := e
    next_dart := hnext
    reverse_zero := by rw [he0,he3]
    color10 := by rw [he1,he0]; exact h01.symm
    color21 := by rw [he2,he1]; exact h12.symm
    label51 := by rw [he5,he1]; exact h51
    label42 := by rw [he4,he2]; exact h42 }⟩

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

namespace Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.TriangleSphere.dipole_of_link_backtrack := @_root_.OAI.Release075.TriangleSphere.dipole_of_link_backtrack
