-- Prove2me | solution 1 for OAI.Release075.FullFilling.trace_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:47:18.06286+00:00
-- url     : https://prove2.me/submissions/cbb7b5b1-aef0-4afa-8b5d-6680ea9df403

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean:L225-L254
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.trace_unique. The node keeps its source
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
import Theorems.Thm_OAI_Release075_FullFilling_fold
import Theorems.Thm_OAI_Release075_FullFilling_trace_empty
import Theorems.Thm_OAI_Release075_FullFilling_trace_mirror
import Theorems.Thm_OAI_Release075_FullFilling_wedge

-- ---- from OAI.GroupTheory.Hyperbolic.Words ----
namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

namespace WordPath
variable {a b c : V} {u v : List E}

theorem source {e : E} {w : List E} (h : WordPath flip color a b (e::w)) :
    color (flip e) = a := by cases h; rfl

theorem append (h : WordPath flip color a b u) (h' : WordPath flip color b c v) :
    WordPath flip color a c (u++v) := by
  induction h with
  | nil => exact h'
  | cons e _ ih => exact .cons e (ih h')

theorem singleton (e : E) : WordPath flip color (color (flip e)) (color e) [e] :=
  .cons e (.nil _)

theorem reverse (hi : Function.Involutive flip) (h : WordPath flip color a b u) :
    WordPath flip color b a (reverseWord flip u) := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih =>
    rw [reverseWord_cons]
    apply ih.append
    have hh := singleton (color := color) (flip := flip) (flip e)
    rwa [hi] at hh

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

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

end OAI

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

theorem trace_reword {w w' : List E} (D : FullFilling flip color face w)
    (h : w = w') (F : E → E → E → M) : (D.reword h).trace F = D.trace F := by
  subst w'; rfl

theorem rotateAppend {u v : List E} (D : FullFilling flip color face (u++v))
    (F : E → E → E → M) :
    ∃ D' : FullFilling flip color face (v++u), D'.trace F = D.trace F := by
  refine ⟨(D.rotate u.length).reword (List.rotate_append_length_eq u v),?_⟩
  rw [trace_reword,trace_rotate]

theorem foldHead (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    {e : E} {w : List E} (D : FullFilling flip color face (e::flip e::w))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face w, D'.trace F = D.trace F := by
  obtain ⟨b,bs,hb,he,hbs⟩ := List.map_eq_cons_iff.mp D.boundary_word
  obtain ⟨a,l,ha,hae,hl⟩ := List.map_eq_cons_iff.mp hbs
  have hbound : D.boundary = b::a::l := by rw [hb,ha]
  have hab : D.label a = flip (D.label b) := by rw [he,hae]
  obtain ⟨D',ht⟩ := D.fold hi hn hbound hab F hdeg
  exact ⟨D'.reword hl,(trace_reword D' hl F).trans ht⟩

theorem erase (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v : List E) (e : E) (D : FullFilling flip color face (u++e::flip e::v))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (u++v), D'.trace F = D.trace F := by
  obtain ⟨D₁,h₁⟩ := D.rotateAppend F
  change FullFilling flip color face (e::flip e::(v++u)) at D₁
  obtain ⟨D₂,h₂⟩ := D₁.foldHead hi hn F hdeg
  obtain ⟨D₃,h₃⟩ := D₂.rotateAppend (u := v) (v := u) F
  exact ⟨D₃,h₃.trans (h₂.trans h₁)⟩

theorem erase_reverse (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v p : List E) (D : FullFilling flip color face (u ++ reverseWord flip p ++ p ++ v))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (u++v), D'.trace F = D.trace F := by
  induction p generalizing u with
  | nil =>
    have he : u ++ reverseWord flip [] ++ [] ++ v = u++v := by
      simp only [reverseWord_nil,List.append_nil]
    exact ⟨D.reword he,trace_reword D he F⟩
  | cons e p ih =>
    have he : u ++ reverseWord flip (e::p) ++ (e::p) ++ v =
        (u++reverseWord flip p) ++ flip e :: flip (flip e) :: (p++v) := by
      simp only [reverseWord_cons,List.append_assoc,List.nil_append,List.cons_append,hi e]
    obtain ⟨D₁,h₁⟩ := (D.reword he).erase hi hn (u++reverseWord flip p) (p++v) (flip e) F hdeg
    have he' : (u++reverseWord flip p) ++ (p++v) =
        u ++ reverseWord flip p ++ p ++ v := by simp only [List.append_assoc]
    obtain ⟨D₂,h₂⟩ := ih u (D₁.reword he')
    exact ⟨D₂,h₂.trans ((trace_reword D₁ he' F).trans (h₁.trans (trace_reword D he F)))⟩

theorem trace_palindrome
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (w : List E) (D : FullFilling flip color face (reverseWord flip w ++ w)) :
    D.trace F = 0 := by
  have he : reverseWord flip w ++ w = [] ++ reverseWord flip w ++ w ++ [] := by
    simp only [List.nil_append,List.append_nil]
  obtain ⟨D',h⟩ := (D.reword he).erase_reverse hi hn [] [] w F hdeg
  rw [trace_reword] at h
  exact h.symm.trans (D'.trace_empty hempty F hrot hmir hdeg)

/-- The signed triangle chain of a full disk depends only on its typed boundary.
This is proved by actual exterior folds, retaining detached components. -/
theorem trace_unique
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    {x : V} {w : List E} (hw : WordPath flip color x x w)
    (D D' : FullFilling flip color face w) : D.trace F = D'.trace F := by
  cases w with
  | nil => rw [trace_empty hempty F hrot hmir hdeg,trace_empty hempty F hrot hmir hdeg]
  | cons e es =>
    let B := D.mirror hi hf
    have hne : reverseWord flip (e::es) ≠ [] := by
      simp only [reverseWord,List.map_eq_nil_iff,List.reverse_eq_nil_iff,
        ne_eq,List.cons_ne_nil,not_false_eq_true]
    obtain ⟨f,fs,he⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨a,l,ha,hal,_⟩ := List.map_eq_cons_iff.mp (B.boundary_word.trans he)
    obtain ⟨b,l',hb,hbl,_⟩ := List.map_eq_cons_iff.mp D'.boundary_word
    have hrev := hw.reverse hi
    rw [he] at hrev
    obtain ⟨C,hC⟩ := B.wedge D' ha hb (by rw [hal,hbl]; exact hrev.source.trans hw.source.symm) F
    have hzero := C.trace_palindrome hempty hi hn F hrot hmir hdeg (e::es)
    have hz : B.trace F + D'.trace F = 0 := hC.symm.trans hzero
    have hm : B.trace F = -D.trace F := D.trace_mirror hi hf F hmir hdeg
    rw [hm] at hz
    exact neg_add_eq_zero.mp hz

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

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.trace_unique := @_root_.OAI.Release075.FullFilling.trace_unique
