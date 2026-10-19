-- Prove2me | solution 1 for OAI.Release075.TriangleSphere.Dipole.delete
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:32:49.81628+00:00
-- url     : https://prove2.me/submissions/057dba75-c442-4914-b1b8-01eef26b9193

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Spheres.lean:L272-L357
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleSphere.Dipole.delete. The node keeps its source
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

-- ---- from OAI.GroupTheory.Hyperbolic.Spheres ----
namespace OAI

namespace Release075
open Equiv PermCycles

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

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

/-- Remove an actual dipole, preserving every additive cyclic antisymmetric
face evaluation. -/
theorem Dipole.delete {D : TriangleSphere flip color face} (P : D.Dipole)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c) :
    ∃ D' : TriangleSphere flip color face,
      Fintype.card D'.Dart < Fintype.card D.Dart ∧ D'.cornerSum F = D.cornerSum F := by
  let e := P.dart
  have h14 : color (D.label (e 1)) = color (D.label (e 4)) := by
    have h := D.color_next (P.dart 1)
    simp only [Perm.mul_apply,P.next_dart,dipoleFace_one,D.reverse_label] at h
    exact h.symm.trans (congrArg color P.label42.symm)
  obtain ⟨r',hi',hn',hp',hc',he',heq,_⟩ :=
    isolate_dipole D.reverse D.next D.reverse_involutive D.reverse_ne
      (color ∘ D.label) D.color_next e P.next_dart P.reverse_zero
      P.color10 P.color21 h14 D.planar
  have hl₁ : ∀ z, D.label (rePair D.reverse (e 1) (e 5) z) = flip (D.label z) :=
    rePair_labels D.reverse D.label flip D.reverse_label
      ((D.reverse_label (e 1)).trans P.label51.symm)
  have hl' : ∀ z, D.label (r' z) = flip (D.label z) := by
    rw [heq]
    exact rePair_labels _ D.label flip hl₁ ((hl₁ (e 2)).trans P.label42.symm)
  let hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant r' dipoleReverse e he' a)
  let hf : ∀ a, (D.next a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant D.next dipoleFace e P.next_dart a)
  let D' : TriangleSphere flip color face := {
    Dart := {a : D.Dart // a ∉ Set.range e}
    reverse := r'.subtypePerm hr
    next := D.next.subtypePerm hf
    reverse_involutive := fun a => Subtype.ext (hi' a.val)
    reverse_ne := fun a h => hn' a.val (congrArg Subtype.val h)
    label := D.label ∘ Subtype.val
    reverse_label := fun a => hl' a.val
    color_next := fun a => hc' a.val
    planar := by
      simpa only [PlanarMap,← Nat.card_eq_fintype_card] using
        hp'.restrict (fun a => a ∉ Set.range e) hr hf
    triangular := fun a => ⟨Subtype.ext (D.triangular a.val).1,
      fun h => (D.triangular a.val).2.1 (congrArg Subtype.val h),(D.triangular a.val).2.2⟩ }
  refine ⟨D',?_,?_⟩
  · exact Fintype.card_subtype_lt (x := e 0) (not_not.mpr ⟨0,rfl⟩)
  let f : D.Dart → M := fun a => F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hcycle (a : D.Dart) : f (D.next a) = f a := by
    have h3' : (D.next^2) (D.next a) = a := by
      simpa only [pow_succ,Perm.mul_apply] using (D.triangular a).1
    change F (D.label (D.next a)) (D.label ((D.next^2) a))
      (D.label ((D.next^2) (D.next a))) = _
    rw [h3']
    exact hrot _ _ _ (D.triangular a).2.2
  have hecycle (j : Fin 6) : f (e (dipoleFace j)) = f (e j) := by
    rw [← P.next_dart]
    exact hcycle _
  have heNext (j : Fin 6) : D.next (e j) = e (dipoleFace j) := P.next_dart j
  have he42 : D.label (e 4) = flip (D.label (e 2)) := P.label42
  have he51 : D.label (e 5) = flip (D.label (e 1)) := P.label51
  have h03 : f (e 3) = - f (e 0) := by
    have hz : D.label (e 3) = flip (D.label (e 0)) := by
      rw [← P.reverse_zero,D.reverse_label]
    have hs (j : Fin 6) : (D.next^2) (e j) = e (dipoleFace (dipoleFace j)) := by
      simp only [pow_two,Perm.mul_apply,heNext]
    simp only [f,heNext,hs,dipoleFace_zero,dipoleFace_one,
      dipoleFace_three,dipoleFace_four]
    rw [hz,he42,he51]
    exact hmir _ _ _ (by simpa only [heNext,hs,dipoleFace_zero,dipoleFace_one] using
      (D.triangular (e 0)).2.2)
  have hsix : ∑ j : Fin 6, f (e j) = 0 := by
    have h1 := hecycle 0
    have h2 := hecycle 1
    have h4 := hecycle 3
    have h5 := hecycle 4
    simp only [dipoleFace_zero,dipoleFace_one,dipoleFace_three,dipoleFace_four] at h1 h2 h4 h5
    simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one]
    change f (e 0)+(f (e 1)+(f (e 2)+(f (e 3)+(f (e 4)+(f (e 5)+0))))) = 0
    rw [h2,h1,h5,h4,h03]
    abel
  have hrange : ∑ a : {a : D.Dart // a ∈ Set.range e}, f a = 0 := by
    have h := (Equiv.ofInjective e e.injective).sum_comp (fun a => f a.val)
    exact h.symm.trans hsix
  have hpart : (∑ a : {a : D.Dart // a ∈ Set.range e}, f a.val) +
      (∑ a : {a : D.Dart // a ∉ Set.range e}, f a.val) = ∑ a, f a := by
    simpa only [Fintype.sum_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] using
      (Equiv.sumCompl (fun a => a ∈ Set.range e)).sum_comp f
  rw [hrange,zero_add] at hpart
  exact hpart

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


theorem solution : type_of% @_root_.OAI.Release075.TriangleSphere.Dipole.delete := @_root_.OAI.Release075.TriangleSphere.Dipole.delete
