-- Prove2me | solution 1 for OAI.Release075.TriangleFilling.dipole_of_link_backtrack
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:02:48.327409+00:00
-- url     : https://prove2.me/submissions/199faa2b-0233-4b01-8ee4-1c744f63ac8f

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean:L187-L245
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleFilling.dipole_of_link_backtrack. The node keeps its source
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
import Theorems.Thm_OAI_Release075_TriangleFilling_reverse_not_sameCycle

-- ---- from OAI.GroupTheory.Hyperbolic.RePairing ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

end Release075.PermCycles

namespace Release075
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.not_mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∉ l ↔ a ∉ l := not_congr (h.mem_iff a)

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

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

/-- Internal reversal of a link walk creates a cancellable pair, when the face
labels are determined by two consecutive sides. -/
theorem dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by
  let a := D.next x
  let b := D.reverse a
  have ha : D.Active a := (D.active_next x).mpr hx
  have hna : a ∉ D.boundary := (D.boundary_cycle.not_mem_iff x).mpr hnx
  have hb : D.Active b := (D.active_reverse a).mpr ha
  obtain ⟨hp,hne,hfa⟩ := D.triangular a ha hna
  obtain ⟨hp',hne',hfb⟩ := D.triangular b hb hnb
  have hx3 := (D.triangular x hx hnx).1
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
  have hab : ¬ D.next.SameCycle a b := D.reverse_not_sameCycle a ha hna hf
  let e := trianglePairEmbedding D.next a b hp hne hp' hne' hab
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := trianglePairEmbedding_values D.next a b hp hne hp' hne' hab
  have hnext : ∀ j, D.next (e j) = e (dipoleFace j) := by
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    have h3' : D.next ((D.next^2) b) = b := by simpa only [pow_succ',Perm.mul_apply] using hp'
    intro j
    fin_cases j <;> first | rfl | exact h3 | exact h3'
  have hnb' : b ∉ D.boundary := hnb
  have hn2a : (D.next^2) a ∉ D.boundary := by
    rw [hax]; exact hnx
  have hn1a : D.next a ∉ D.boundary := (D.boundary_cycle.not_mem_iff a).mpr hna
  have hn1b : D.next b ∉ D.boundary := (D.boundary_cycle.not_mem_iff b).mpr hnb'
  have hn2b : (D.next^2) b ∉ D.boundary :=
    (D.boundary_cycle.not_mem_iff (D.next b)).mpr hn1b
  obtain ⟨h01,h12,_⟩ := hf _ _ _ hfa
  refine ⟨{
    dart := e
    next_dart := hnext
    reverse_zero := by rw [he0,he3]
    not_boundary := by
      intro j
      fin_cases j <;> assumption
    active := by rw [he0]; exact ha
    color10 := by rw [he1,he0]; exact h01.symm
    color21 := by rw [he2,he1]; exact h12.symm
    label51 := by rw [he5,he1]; exact h51
    label42 := by rw [he4,he2]; exact h42 }⟩

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


theorem solution : type_of% @_root_.OAI.Release075.TriangleFilling.dipole_of_link_backtrack := @_root_.OAI.Release075.TriangleFilling.dipole_of_link_backtrack
