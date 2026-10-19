-- Prove2me | solution 1 for OAI.Release075.FullFilling.fold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:42:44.716991+00:00
-- url     : https://prove2.me/submissions/bd9597c1-bfd5-45e7-a387-7d8fe2e34a44

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean:L259-L325
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.fold. The node keeps its source
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
import Theorems.Thm_OAI_Release075_IsBoundary_erase_pair
import Theorems.Thm_OAI_Release075_PermCycles_fold_pair

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

theorem same_outside_boundary_pow {f g : Perm A} {l : List A}
    (hb : IsBoundary f l) (he : ∀ z, z ∉ l → g z = f z)
    {a : A} (ha : a ∉ l) (n : ℕ) : (g^n) a = (f^n) a := by
  have ho (k : ℕ) : (f^k) a ∉ l := by
    induction k with
    | zero => exact ha
    | succ k ih =>
      rw [pow_succ',Perm.mul_apply]
      exact (hb.not_mem_iff _).mpr ih
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Perm.mul_apply,ih,he _ (ho n)]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem components_pred [Fintype A] (r f : Perm A) (p : A → Prop)
    (hr : ∀ a, p (r a) ↔ p a) (hf : ∀ a, p (f a) ↔ p a)
    {a b : A} (h : components r f a b) : p a ↔ p b := by
  have hh : components r f ≤ Setoid.ker p := by
    apply sup_le
    · intro x y h; exact propext (invariant_pred_sameCycle r p hr h)
    · intro x y h; exact propext (invariant_pred_sameCycle f p hf h)
  exact propext_iff.mp (hh h)

theorem pair_invariant (f : Perm A) {a b : A} (ha : f a = b) (hb : f b = a) (z : A) :
    (f z = a ∨ f z = b) ↔ (z = a ∨ z = b) := by
  constructor
  · rintro (h | h)
    · exact Or.inr (f.injective (h.trans hb.symm))
    · exact Or.inl (f.injective (h.trans ha.symm))
  · rintro (rfl | rfl)
    · exact Or.inr ha
    · exact Or.inl hb

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

-- ---- from OAI.GroupTheory.Hyperbolic.FullFilling ----
namespace OAI

namespace Release075
open Equiv PermCycles

attribute [instance] FullFilling.dartFintype

namespace TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end TriangleFilling

namespace FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : FullFilling flip color face w)

end FullFilling
end Release075

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

omit [AddCommGroup M] in
theorem bigon_component {w : List E} (D : FullFilling flip color face w)
    {a b : D.Dart} (ha : D.Bigon a) (h : components D.reverse D.next a b) :
    b = a ∨ b = D.reverse a := by
  have hn : D.next (D.reverse a) = a := by rw [← ha.1]; exact ha.2
  exact (components_pred D.reverse D.next (fun z => z=a ∨ z=D.reverse a)
    (pair_invariant D.reverse rfl (D.reverse_involutive a))
    (pair_invariant D.next ha.1 hn) h).mp (Or.inl rfl)

/-- Exterior cancellation retains all components and preserves the face chain. -/
theorem fold {w : List E} (D : FullFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) (F : E → E → E → M)
    (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (l.map D.label), D'.trace F = D.trace F := by
  have hbound : IsBoundary D.next (b::a::l) := hb ▸ D.boundary_cycle
  have hab : a ≠ b := fun h => hbound.1.notMem (by simp [h])
  have hba : D.next b = a := by simpa using hbound.step 0 (by simp)
  obtain ⟨r',f',hi',hn',hp',hl',hc',hra,hrb,hfa,hfb,hm,_,heq⟩ :=
    fold_pair D.reverse D.next D.reverse_involutive D.reverse_ne D.label flip hflip
      color hne D.reverse_label D.color_next D.planar hab hba hl
  have hrest := hbound.erase_pair
  rw [←heq] at hrest
  let D' : FullFilling flip color face (l.map D.label) := {
    Dart := D.Dart
    reverse := r'
    next := f'
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := l
    boundary_cycle := hrest.1
    boundary_word := rfl
    cells := by
      intro z hz
      by_cases hza : z = a
      · subst z
        exact Or.inr ⟨hfa.trans hra.symm,by simp only [pow_two,Perm.mul_apply,hfa,hfb]⟩
      by_cases hzb : z = b
      · subst z
        exact Or.inr ⟨hfb.trans hrb.symm,by simp only [pow_two,Perm.mul_apply,hfa,hfb]⟩
      have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
      have hstep := hrest.2 z hzo
      have he (n : ℕ) := same_outside_boundary_pow hbound hrest.2 hzo n
      rcases D.cells z (by rwa [hb]) with ht | hg
      · exact Or.inl ⟨(he 3).trans ht.1,hstep ▸ ht.2.1,by
          simpa only [hstep,he 2] using ht.2.2⟩
      · have hrz : r' z = D.reverse z := by
          apply (D.bigon_component hg (hm ?_)).resolve_left (hn' z)
          exact (show Perm.SameCycle.setoid r' ≤ components r' f' from le_sup_left)
            (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' z))
        exact Or.inr ⟨hstep.trans (hg.1.trans hrz.symm),(he 2).trans hg.2⟩ }
  refine ⟨D',?_⟩
  unfold trace
  apply Finset.sum_congr rfl
  intro z _
  change (if z ∈ l then 0 else F (D.label z) (D.label (f' z)) (D.label ((f'^2) z))) = _
  by_cases hz : z ∈ l
  · have hzo : z ∈ D.boundary := by rw [hb]; simp only [List.mem_cons]; tauto
    simp only [hz,hzo,ite_true]
  by_cases hza : z = a
  · subst z
    have hzo : a ∈ D.boundary := by rw [hb]; simp
    simp only [hz,hzo,ite_false,ite_true,pow_two,Perm.mul_apply,hfa,hfb,hdeg]
  by_cases hzb : z = b
  · subst z
    have hzo : b ∈ D.boundary := by rw [hb]; simp
    simp only [hz,hzo,ite_false,ite_true,pow_two,Perm.mul_apply,hfa,hfb,hdeg]
  have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
  have hD : z ∉ D.boundary := by rwa [hb]
  simp only [hz,hD,ite_false,hrest.2 z hzo,
    same_outside_boundary_pow hbound hrest.2 hzo 2]

end Release075.FullFilling

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.fold := @_root_.OAI.Release075.FullFilling.fold
