-- Prove2me | solution 1 for OAI.Release075.IsBoundary.erase_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:52:50.655773+00:00
-- url     : https://prove2.me/submissions/d30521ce-8be9-46fd-9036-3b4d2b55d716

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean:L125-L157
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.IsBoundary.erase_pair. The node keeps its source
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

theorem formPerm_append_cons (x y : A) (xs ys : List A) :
    (x :: xs ++ y :: ys).formPerm = (x :: xs).formPerm *
      Equiv.swap ((x::xs).getLast (by simp)) y * (y::ys).formPerm := by
  induction xs generalizing x with
  | nil => simp only [List.cons_append,List.nil_append,List.formPerm_cons_cons,List.formPerm_singleton,
      List.getLast_singleton,one_mul]
  | cons z xs ih =>
    simpa only [List.cons_append,List.formPerm_cons_cons,List.getLast_cons_cons,mul_assoc] using
      congrArg (fun p : Perm A => Equiv.swap x z * p) (ih z)

theorem formPerm_concat (x y : A) (xs ys : List A) (hy : y ∉ x::xs) :
    (x :: xs ++ y :: ys).formPerm =
      Equiv.swap x y * ((x::xs).formPerm * (y::ys).formPerm) := by
  rw [formPerm_append_cons,Equiv.mul_swap_eq_swap_mul,
    List.formPerm_apply_getLast,List.formPerm_apply_of_notMem hy,mul_assoc]

theorem IsBoundary.not_mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∉ l ↔ a ∉ l := not_congr (h.mem_iff a)

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.TriangleFilling ----
namespace OAI

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

attribute [instance] TriangleFilling.finiteDart

namespace TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end TriangleFilling
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

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.step {f : Perm A} {l : List A} (h : IsBoundary f l)
    (n : ℕ) (hn : n+1 < l.length) : f l[n] = l[n+1] := by
  rw [h.2 _ (List.getElem_mem _)]
  exact List.formPerm_apply_lt_getElem l h.1 n hn

theorem IsBoundary.erase_pair {f : Perm A} {a b : A} {l : List A}
    (h : IsBoundary f (b::a::l)) :
    IsBoundary (Equiv.swap b (f a)*f) l ∧
    (∀ z, z ∉ b::a::l → (Equiv.swap b (f a)*f) z = f z) := by
  constructor
  · refine ⟨h.1.of_cons.of_cons,?_⟩
    intro z hz
    cases l with
    | nil => simp at hz
    | cons c cs =>
      have hfa : f a = c := h.step 1 (by simp)
      have hcb : c ∉ [b,a] := by
        have hh := h.1
        simp only [List.nodup_cons,List.mem_cons] at hh ⊢
        tauto
      have hperm : (b::a::c::cs : List A).formPerm =
          Equiv.swap b c * (Equiv.swap b a * (c::cs).formPerm) := by
        simpa only [List.formPerm_pair, List.cons_append, List.nil_append] using formPerm_concat b c [a] cs hcb
      have hmem : (c::cs).formPerm z ∈ c::cs := List.formPerm_apply_mem_of_mem hz
      have hnb : (c::cs).formPerm z ≠ b := by
        intro he; apply h.1.notMem; rw [←he]; exact List.mem_cons_of_mem a hmem
      have hna : (c::cs).formPerm z ≠ a := by
        intro he; apply h.1.of_cons.notMem; rwa [←he]
      have hzfull : z ∈ b::a::c::cs := List.mem_cons_of_mem b (List.mem_cons_of_mem a hz)
      rw [Perm.mul_apply, hfa, h.2 z hzfull, hperm]
      simp only [Perm.mul_apply, Equiv.swap_apply_self,
        Equiv.swap_apply_of_ne_of_ne hnb hna]
  · intro z hz
    have hfz := (h.not_mem_iff z).mpr hz
    have hfa := (h.mem_iff a).mpr (by simp)
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; apply hfz; simp [he]
    · intro he; apply hfz; rwa [he]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq

end Release075.PermCycles

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

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

namespace Fillable

end Fillable
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.IsBoundary.erase_pair := @_root_.OAI.Release075.IsBoundary.erase_pair
