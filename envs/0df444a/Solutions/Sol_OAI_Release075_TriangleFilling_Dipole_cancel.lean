-- Prove2me | solution 1 for OAI.Release075.TriangleFilling.Dipole.cancel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:59:38.426701+00:00
-- url     : https://prove2.me/submissions/971d67f9-0528-4df6-85be-794c34e546b5

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean:L26-L84
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleFilling.Dipole.cancel. The node keeps its source
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
import Theorems.Thm_OAI_Release075_PermCycles_isolate_dipole

-- ---- from OAI.GroupTheory.Hyperbolic.Planarity ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem color_swap {C : Type*} (color : A → C) {a b : A}
    (hab : color a = color b) (z : A) : color (Equiv.swap a b z) = color z := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

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

end OAI

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

omit [Fintype A] in
theorem range_invariant {B : Type*} (r : Perm A) (t : Perm B) (e : B → A)
    (he : ∀ b, r (e b) = e (t b)) (a : A) : r a ∈ Set.range e ↔ a ∈ Set.range e := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨t⁻¹ b,r.injective ?_⟩
    rw [he]
    change e (t (t.symm b)) = r a
    rwa [t.apply_symm_apply]
  · rintro ⟨b,rfl⟩
    exact ⟨t b,(he b).symm⟩

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem rePair_labels {E : Type*} (r : Perm A) (label : A → E) (flip : E → E)
    (hr : ∀ a, label (r a) = flip (label a)) {a b : A}
    (hl : label (r a) = label b) :
    ∀ z, label (rePair r a b z) = flip (label z) := by
  intro z
  simp only [rePair,Perm.mul_apply,color_swap label hl,hr]

end Release075.PermCycles

namespace Release075
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

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

-- ---- from OAI.GroupTheory.Hyperbolic.Dipoles ----
namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- A labeled cancellation decreases the number of active darts. The isolated
pair remains harmlessly as a component disjoint from the prescribed boundary. -/
theorem Dipole.cancel {w : List E} {D : TriangleFilling flip color face w} (P : D.Dipole) :
    ∃ D' : TriangleFilling flip color face w, D'.activeCount < D.activeCount := by
  let e := P.dart
  have h14 : color (D.label (e 1)) = color (D.label (e 4)) := by
    have h := D.color_next (P.dart 1)
    simp only [Perm.mul_apply,P.next_dart,dipoleFace_one,D.reverse_label] at h
    exact h.symm.trans (congrArg color P.label42.symm)
  obtain ⟨r',hi',hn',hp',hc',he',heq,hm⟩ :=
    isolate_dipole D.reverse D.next D.reverse_involutive D.reverse_ne
      (color ∘ D.label) D.color_next e P.next_dart P.reverse_zero
      P.color10 P.color21 h14 D.planar
  have hl₁ : ∀ z, D.label (rePair D.reverse (e 1) (e 5) z) = flip (D.label z) :=
    rePair_labels D.reverse D.label flip D.reverse_label
      ((D.reverse_label (e 1)).trans P.label51.symm)
  have hl' : ∀ z, D.label (r' z) = flip (D.label z) := by
    rw [heq]
    exact rePair_labels _ D.label flip hl₁ ((hl₁ (e 2)).trans P.label42.symm)
  let D' : TriangleFilling flip color face w := {
    Dart := D.Dart
    reverse := r'
    next := D.next
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := D.boundary
    boundary_cycle := D.boundary_cycle
    boundary_word := D.boundary_word
    triangular := by
      intro z hz hn
      obtain ⟨b,hb,hzb⟩ := hz
      exact D.triangular z ⟨b,hb,hm hzb⟩ hn }
  refine ⟨D',?_⟩
  have hle : ∀ z, D'.Active z → D.Active z := by
    rintro z ⟨b,hb,hzb⟩
    exact ⟨b,hb,hm hzb⟩
  have hnot : ¬ D'.Active (e 0) := by
    rintro ⟨b,hb,heb⟩
    have hmem : b ∈ Set.range e := (components_pred r' D.next (fun z => z ∈ Set.range e)
      (range_invariant r' dipoleReverse e he')
      (range_invariant D.next dipoleFace e P.next_dart) heb).mp ⟨0,rfl⟩
    obtain ⟨j,rfl⟩ := hmem
    exact P.not_boundary j hb
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact hle z hz
  · intro he
    have hmem : e 0 ∈ Finset.univ.filter D.Active := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact P.active
    rw [← he] at hmem
    exact hnot (Finset.mem_filter.mp hmem).2

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


theorem solution : type_of% @_root_.OAI.Release075.TriangleFilling.Dipole.cancel := @_root_.OAI.Release075.TriangleFilling.Dipole.cancel
