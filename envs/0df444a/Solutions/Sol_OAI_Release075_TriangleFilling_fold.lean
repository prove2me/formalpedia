-- Prove2me | solution 1 for OAI.Release075.TriangleFilling.fold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:54:28.279966+00:00
-- url     : https://prove2.me/submissions/305457c5-cfda-467f-bd0c-d64b65652aee

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean:L205-L253
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleFilling.fold. The node keeps its source
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

/-- A genuine reverse-edge deletion, retaining the external word even when the
outside partners reconnect. The detached tree is an ignored separate component. -/
theorem fold {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) :
    Nonempty (TriangleFilling flip color face (l.map D.label)) := by
  have hbound : IsBoundary D.next (b::a::l) := hb ▸ D.boundary_cycle
  have hab : a ≠ b := fun h => hbound.1.notMem (by simp [h])
  have hba : D.next b = a := by simpa using hbound.step 0 (by simp)
  obtain ⟨r',f',hi',hn',hp',hl',hc',hra,hrb,hfa,hfb,hm,_,heq⟩ :=
    fold_pair D.reverse D.next D.reverse_involutive D.reverse_ne D.label flip hflip
      color hne D.reverse_label D.color_next D.planar hab hba hl
  have hrest := hbound.erase_pair
  rw [←heq] at hrest
  have hnot (z : D.Dart) (hz : z ∈ l) : ¬(z = a ∨ z = b) := by
    rintro (rfl | rfl)
    · exact hbound.1.of_cons.notMem hz
    · exact hbound.1.notMem (List.mem_cons_of_mem a hz)
  refine ⟨{
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
    triangular := ?_ }⟩
  intro z hz hzl
  obtain ⟨c,hcl,hzc⟩ := hz
  have hnotpair : ¬(z = a ∨ z = b) := by
    intro hp
    exact hnot c hcl ((components_pred r' f' (fun x => x=a ∨ x=b)
      (pair_invariant r' hra hrb) (pair_invariant f' hfa hfb) hzc).mp hp)
  have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
  have htri := D.triangular z ⟨c,by rw [hb]; simp only [List.mem_cons]; tauto,hm hzc⟩
    (by rwa [hb])
  have he (n : ℕ) := same_outside_boundary_pow hbound hrest.2 hzo n
  refine ⟨?_,?_,?_⟩
  · rw [he 3]; exact htri.1
  · have hstep : f' z = D.next z := hrest.2 z hzo
    rw [hstep]
    exact htri.2.1
  · simpa only [hrest.2 z hzo,he 2] using htri.2.2

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
open OAI OAI.Release075 OAI.Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.TriangleFilling.fold := @_root_.OAI.Release075.TriangleFilling.fold
