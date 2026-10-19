-- Prove2me | solution 1 for OAI.Release075.PermCycles.fold_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:51:14.432981+00:00
-- url     : https://prove2.me/submissions/e6bd4e8a-b043-4749-9c94-5dcb6c24da6b

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/RePairing.lean:L435-L496
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.fold_pair. The node keeps its source
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
import Theorems.Thm_OAI_Release075_PermCycles_PlanarMap_swap_left
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

omit [Fintype A] in
theorem components_comm (f g : Perm A) : components f g = components g f := sup_comm _ _

omit [Fintype A] in
theorem componentCount_comm (f g : Perm A) : componentCount f g = componentCount g f := by
  simp only [componentCount,components_comm f g]

theorem PlanarMap.symm {f g : Perm A} (h : PlanarMap f g) : PlanarMap g f := by
  simpa only [PlanarMap,cycleCount_mul_comm g f,componentCount_comm g f,
    Nat.add_comm (cycleCount g) (cycleCount f)] using h

theorem PlanarMap.swap_right {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : g.SameCycle a b) : PlanarMap f (Equiv.swap a b * g) :=
  (hp.symm.swap_left hab).symm

omit [Fintype A] in
theorem swap_color_preserving {C : Type*} (r f : Perm A) (color : A → C)
    (hc : ∀ a, color ((r*f) a) = color a) {a b : A}
    (hab : color (r a) = color (r b)) :
    ∀ z, color ((r*(Equiv.swap a b * f)) z) = color z := by
  intro z
  change (color ∘ r) (Equiv.swap a b (f z)) = color z
  rw [color_swap (color ∘ r) hab]
  exact hc z

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

theorem components_rePair_le (r f : Perm A) {a b : A}
    (h : components r f (r a) b) : components (rePair r a b) f ≤ components r f := by
  rw [components_conjugate_swap r f h]
  exact le_joinPair _ _ _

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

theorem components_split_right_le (r f : Perm A) {a b : A}
    (h : f.SameCycle a b) : components r (Equiv.swap a b*f) ≤ components r f := by
  by_cases he : a = b
  · subst b
    simp only [Equiv.swap_self]
    change components r (1*f) ≤ components r f
    rw [one_mul]
  have hn := swap_splits f he h
  have hj := components_swap_of_not_same (Equiv.swap a b*f) r hn
  have hr : Equiv.swap a b * (Equiv.swap a b*f) = f := by
    rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  rw [hr,components_comm f r,components_comm (Equiv.swap a b*f) r] at hj
  rw [hj]
  exact le_joinPair _ a b

/-- Fold two consecutive inverse boundary incidences. Darts are first paired,
then split off as their own isolated tree component. The surviving outside word
is unchanged; no disjointness of the former outside partners is assumed. -/
theorem fold_pair {C E : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ a, r a ≠ a)
    (label : A → E) (flip : E → E) (hflip : Function.Involutive flip)
    (color : E → C) (hedge : ∀ e, color e ≠ color (flip e))
    (hl : ∀ a, label (r a) = flip (label a))
    (hc : ∀ a, color (label ((r*f) a)) = color (label a))
    (hp : PlanarMap r f) {a b : A} (hab : a ≠ b)
    (hf : f b = a) (he : label a = flip (label b)) :
    ∃ r' f' : Perm A,
      Function.Involutive r' ∧ (∀ z, r' z ≠ z) ∧ PlanarMap r' f' ∧
      (∀ z, label (r' z) = flip (label z)) ∧
      (∀ z, color (label ((r'*f') z)) = color (label z)) ∧
      r' a = b ∧ r' b = a ∧ f' a = b ∧ f' b = a ∧
      components r' f' ≤ components r f ∧
      (∀ z, f z ≠ b → f z ≠ f a → f' z = f z) ∧
      f' = Equiv.swap b (f a) * f := by
  have hleft : (color ∘ label) (r a) = (color ∘ label) b := by
    dsimp; rw [hl,he,hflip]
  have hright : (color ∘ label) a = (color ∘ label) (r b) := by
    dsimp; rw [hl,he]
  have hcol : (color ∘ label) a ≠ (color ∘ label) b := by
    dsimp; rw [he]; exact (hedge (label b)).symm
  have hcy : (r*f).SameCycle (r a) b := by
    have h := Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) b)
    simpa only [Perm.mul_apply,hf] using h.symm
  let r' := rePair r a b
  have hi' := rePair_involutive r hi a b
  have hn' := rePair_ne r hn a b
  have hp' : PlanarMap r' f := planar_rePair_allow r f hi hn (color ∘ label) hc
    hcol hleft hright hcy hp
  have hc' : ∀ z, color (label ((r'*f) z)) = color (label z) :=
    rePair_color r f hi (color ∘ label) hc hleft hright
  have ha : r' a = b := rePair_apply_a r hn hab
  have hb : r' b = a := by rw [←ha,hi']
  have hlabel : ∀ z, label (r' z) = flip (label z) := rePair_labels r label flip hl
    (by rw [hl,he,hflip])
  let f' := Equiv.swap b (f a) * f
  have hcyf : f.SameCycle b (f a) := by
    have hh : f.SameCycle b a := by
      simpa only [hf] using (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f b))
    exact Perm.sameCycle_apply_right.mpr hh
  have hp'' : PlanarMap r' f' := hp'.swap_right hcyf
  have ha' : f' a = b := Equiv.swap_apply_right b (f a)
  have hb' : f' b = a := by
    change Equiv.swap b (f a) (f b) = a
    rw [hf,Equiv.swap_apply_of_ne_of_ne hab]
    intro h
    have := f.injective (h.symm.trans hf.symm)
    exact hab this
  have hswap : color (label (r' b)) = color (label (r' (f a))) := by
    rw [hb]
    exact (hc' a).symm
  have hmono : components r' f' ≤ components r f :=
    (components_split_right_le r' f hcyf).trans
      (components_rePair_le r f (sameCycle_mul_le_components r f hcy))
  refine ⟨r',f',hi',hn',hp'',hlabel,
    swap_color_preserving r' f (color ∘ label) hc' hswap,ha,hb,ha',hb',hmono,?_,rfl⟩
  intro z hz₁ hz₂
  exact Equiv.swap_apply_of_ne_of_ne hz₁ hz₂

end Release075.PermCycles

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.fold_pair := @_root_.OAI.Release075.PermCycles.fold_pair
