-- Prove2me | solution 1 for OAI.Release075.PermCycles.isolate_dipole
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:49:33.105984+00:00
-- url     : https://prove2.me/submissions/0fb4364f-6773-4f77-b1e9-f374835cca5e

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/RePairing.lean:L184-L277
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.isolate_dipole. The node keeps its source
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
import Theorems.Thm_OAI_Release075_PermCycles_components_conjugate_swap
import Theorems.Thm_OAI_Release075_PermCycles_planar_rePair

-- ---- from OAI.GroupTheory.Hyperbolic.Planarity ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem rePair_vertex (reverse face : Perm A) (hi : Function.Involutive reverse) (a b : A) :
    rePair reverse a b * face =
      Equiv.swap (reverse a) b * Equiv.swap a (reverse b) * (reverse * face) := by
  unfold rePair
  rw [mul_assoc (Equiv.swap (reverse a) b) reverse (Equiv.swap (reverse a) b),
    Equiv.mul_swap_eq_swap_mul reverse (reverse a) b,hi a]
  simp only [mul_assoc]

omit [Fintype A] in
theorem rePair_involutive (reverse : Perm A) (hi : Function.Involutive reverse) (a b : A) :
    Function.Involutive (rePair reverse a b) := by
  intro z
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_self]
  rw [hi,Equiv.swap_apply_self]

omit [Fintype A] in
theorem rePair_ne (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) (a b z : A) :
    rePair reverse a b z ≠ z := by
  intro h
  have hh := congrArg (Equiv.swap (reverse a) b) h
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_self] at hh
  exact hn _ hh

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

omit [Fintype A] in
theorem rePair_apply_a (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) {a b : A}
    (hab : a ≠ b) : rePair reverse a b a = b := by
  simp only [rePair,Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (hn a).symm hab,Equiv.swap_apply_left]

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
theorem rePair_color {C : Type*} (r f : Perm A) (hi : Function.Involutive r)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z) {a b : A}
    (hl : color (r a) = color b) (hr : color a = color (r b)) :
    ∀ z, color ((rePair r a b*f) z) = color z := by
  intro z
  rw [rePair_vertex r f hi]
  change color (Equiv.swap (r a) b (Equiv.swap a (r b) ((r*f) z))) = color z
  rw [color_swap color hl,color_swap color hr,hc]

theorem planar_rePair_allow {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    {a b : A} (hab : color a ≠ color b)
    (hl : color (r a) = color b) (hr : color a = color (r b))
    (hcy : (r*f).SameCycle (r a) b) (hp : PlanarMap r f) :
    PlanarMap (rePair r a b) f := by
  by_cases h : r a = b
  · have hr : rePair r a b = r := by
      unfold rePair
      rw [h,Equiv.swap_self]
      change 1 * r * 1 = r
      simp
    rwa [hr]
  · exact planar_rePair r f hi hn color hc hab hl hr h hcy hp

omit [Fintype A] in
theorem rePair_other_edge (r : Perm A) (hi : Function.Involutive r) {a b z : A}
    (hza : z ≠ a) (hzb : z ≠ b) (hra : r z ≠ a) (hrb : r z ≠ b) :
    rePair r a b z = r z := by
  have hzra : z ≠ r a := by intro h; apply hra; rw [h,hi]
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hzra hzb,
    Equiv.swap_apply_of_ne_of_ne (r.injective.ne hza) hrb]

theorem components_rePair_le (r f : Perm A) {a b : A}
    (h : components r f (r a) b) : components (rePair r a b) f ≤ components r f := by
  rw [components_conjugate_swap r f h]
  exact le_joinPair _ _ _

/-- The actual two re-pairings isolate the cancellable six darts. This lemma
retains arbitrary outside reconnections; it does not postulate an empty outside
neighborhood. All unaffected face orbits, including the exterior, are unchanged. -/
theorem isolate_dipole {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    (e : Fin 6 ↪ A) (hf : ∀ j, f (e j) = e (dipoleFace j))
    (he : r (e 0) = e 3)
    (h10 : color (e 1) ≠ color (e 0)) (h21 : color (e 2) ≠ color (e 1))
    (h14 : color (e 1) = color (e 4)) (hp : PlanarMap r f) :
    ∃ r' : Perm A, Function.Involutive r' ∧ (∀ z, r' z ≠ z) ∧
      PlanarMap r' f ∧ (∀ z, color ((r'*f) z) = color z) ∧
      (∀ j, r' (e j) = e (dipoleReverse j)) ∧
      r' = rePair (rePair r (e 1) (e 5)) (e 2) (e 4) ∧
      components r' f ≤ components r f := by
  have h3 : r (e 3) = e 0 := by rw [← he,hi]
  have hne {i j : Fin 6} (h : i ≠ j) : e i ≠ e j := e.injective.ne h
  have hF0 : f (e 0) = e 1 := by simpa using hf 0
  have hF1 : f (e 1) = e 2 := by simpa using hf 1
  have hF2 : f (e 2) = e 0 := by simpa using hf 2
  have hF3 : f (e 3) = e 4 := by simpa using hf 3
  have hF4 : f (e 4) = e 5 := by simpa using hf 4
  have hF5 : f (e 5) = e 3 := by simpa using hf 5
  have h50 : color (e 5) = color (e 0) := by
    simpa only [Perm.mul_apply,hF5,h3] using (hc (e 5)).symm
  have h23 : color (e 2) = color (e 3) := by
    simpa only [Perm.mul_apply,hF2,he] using (hc (e 2)).symm
  have hl₁ : color (r (e 1)) = color (e 5) := by
    rw [h50]
    simpa only [Perm.mul_apply,hF0] using hc (e 0)
  have hr₁ : color (e 1) = color (r (e 5)) := by
    rw [h14]
    simpa only [Perm.mul_apply,hF4] using (hc (e 4)).symm
  have hcy₁ : (r*f).SameCycle (r (e 1)) (e 5) := by
    have hA : (r*f).SameCycle (e 0) (r (e 1)) := by
      simpa only [Perm.mul_apply,hF0] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) (e 0)))
    have hB : (r*f).SameCycle (e 5) (e 0) := by
      simpa only [Perm.mul_apply,hF5,h3] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) (e 5)))
    exact (hB.trans hA).symm
  let r₁ := rePair r (e 1) (e 5)
  have hi₁ : Function.Involutive r₁ := rePair_involutive r hi _ _
  have hn₁ : ∀ z, r₁ z ≠ z := rePair_ne r hn _ _
  have hp₁ : PlanarMap r₁ f := planar_rePair_allow r f hi hn color hc
    (by rwa [h50]) hl₁ hr₁ hcy₁ hp
  have hc₁ : ∀ z, color ((r₁*f) z) = color z := rePair_color r f hi color hc hl₁ hr₁
  have h01 : r₁ (e 0) = e 3 := by
    rw [rePair_other_edge r hi (hne (by decide)) (hne (by decide))
      (by rw [he]; exact hne (by decide)) (by rw [he]; exact hne (by decide)),he]
  have h31 : r₁ (e 3) = e 0 := by rw [← h01,hi₁]
  have h15 : r₁ (e 1) = e 5 := rePair_apply_a r hn (hne (by decide))
  have h51 : r₁ (e 5) = e 1 := by rw [← h15,hi₁]
  have hl₂ : color (r₁ (e 2)) = color (e 4) := by
    rw [← h14]
    simpa only [Perm.mul_apply,hF1] using hc₁ (e 1)
  have hr₂ : color (e 2) = color (r₁ (e 4)) := by
    rw [h23]
    simpa only [Perm.mul_apply,hF3] using (hc₁ (e 3)).symm
  have hcy₂ : (r₁*f).SameCycle (r₁ (e 2)) (e 4) := by
    have hA : (r₁*f).SameCycle (e 1) (r₁ (e 2)) := by
      simpa only [Perm.mul_apply,hF1] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r₁*f) (e 1)))
    have hB : (r₁*f).SameCycle (e 4) (e 1) := by
      simpa only [Perm.mul_apply,hF4,h51] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r₁*f) (e 4)))
    exact (hB.trans hA).symm
  let r₂ := rePair r₁ (e 2) (e 4)
  have hi₂ : Function.Involutive r₂ := rePair_involutive r₁ hi₁ _ _
  have hn₂ : ∀ z, r₂ z ≠ z := rePair_ne r₁ hn₁ _ _
  have hp₂ : PlanarMap r₂ f := planar_rePair_allow r₁ f hi₁ hn₁ color hc₁
    (by rwa [← h14]) hl₂ hr₂ hcy₂ hp₁
  have hc₂ : ∀ z, color ((r₂*f) z) = color z := rePair_color r₁ f hi₁ color hc₁ hl₂ hr₂
  have h02 : r₂ (e 0) = e 3 := by
    rw [rePair_other_edge r₁ hi₁ (hne (by decide)) (hne (by decide))
      (by rw [h01]; exact hne (by decide)) (by rw [h01]; exact hne (by decide)),h01]
  have h12 : r₂ (e 1) = e 5 := by
    rw [rePair_other_edge r₁ hi₁ (hne (by decide)) (hne (by decide))
      (by rw [h15]; exact hne (by decide)) (by rw [h15]; exact hne (by decide)),h15]
  have h24 : r₂ (e 2) = e 4 := rePair_apply_a r₁ hn₁ (hne (by decide))
  refine ⟨r₂,hi₂,hn₂,hp₂,hc₂,?_,rfl,?_⟩
  · intro j
    fin_cases j
    · simpa using h02
    · simpa using h12
    · simpa using h24
    · change r₂ (e 3) = e (dipoleReverse 3)
      simp only [dipoleReverse_three]; rw [← h02,hi₂]
    · change r₂ (e 4) = e (dipoleReverse 4)
      simp only [dipoleReverse_four]; rw [← h24,hi₂]
    · change r₂ (e 5) = e (dipoleReverse 5)
      simp only [dipoleReverse_five]; rw [← h12,hi₂]
  · exact (components_rePair_le r₁ f (sameCycle_mul_le_components r₁ f hcy₂)).trans
      (components_rePair_le r f (sameCycle_mul_le_components r f hcy₁))

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

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.isolate_dipole := @_root_.OAI.Release075.PermCycles.isolate_dipole
