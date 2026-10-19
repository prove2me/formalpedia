-- Prove2me | solution 1 for OAI.Release075.PermCycles.planar_rePair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:44:58.493366+00:00
-- url     : https://prove2.me/submissions/c56b20bf-677b-4d6b-a331-2b53208f3a19

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Planarity.lean:L153-L239
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.planar_rePair. The node keeps its source
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
import Theorems.Thm_OAI_Release075_PermCycles_components_conjugate_swap
import Theorems.Thm_OAI_Release075_PermCycles_swap_sameCycle_away

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
theorem cycleCount_conj (f t : Perm A) : cycleCount (t*f*t⁻¹) = cycleCount f := by
  let e : Cycles f ≃ Cycles (t*f*t⁻¹) := Quotient.congr t (by
    intro x y
    change f.SameCycle x y ↔ (t*f*t⁻¹).SameCycle (t x) (t y)
    simp [Perm.sameCycle_conj])
  exact (Nat.card_congr e).symm

omit [Fintype A] in
theorem cycleCount_rePair (reverse : Perm A) (a b : A) :
    cycleCount (rePair reverse a b) = cycleCount reverse := by
  simpa only [rePair,Equiv.swap_inv] using cycleCount_conj reverse (Equiv.swap (reverse a) b)

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

omit [Fintype A] in
theorem rePair_apply_reverse_a (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) {a b : A}
    (hab : a ≠ b) : rePair reverse a b (reverse a) = reverse b := by
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne (reverse.injective.ne hab.symm) (hn b)

theorem planar_rePair {C : Type*} (reverse face : Perm A)
    (hi : Function.Involutive reverse) (hn : ∀ z, reverse z ≠ z)
    (color : A → C) (hcolor : ∀ z, color ((reverse*face) z) = color z)
    {a b : A} (hab : color a ≠ color b)
    (hleft : color (reverse a) = color b) (hright : color a = color (reverse b))
    (hpair : reverse a ≠ b) (hcycle : (reverse*face).SameCycle (reverse a) b)
    (hplanar : PlanarMap reverse face) : PlanarMap (rePair reverse a b) face := by
  let v := reverse * face
  let r' := rePair reverse a b
  let v' := r' * face
  let u := Equiv.swap a (reverse b) * v
  have hab' : a ≠ b := fun h => hab (congrArg color h)
  have hcountR : cycleCount r' = cycleCount reverse := cycleCount_rePair reverse a b
  have hv' : v' = Equiv.swap (reverse a) b * u := rePair_vertex reverse face hi a b
  have haway1 : color (reverse a) ≠ color a := by rw [hleft]; exact hab.symm
  have haway2 : color (reverse a) ≠ color (reverse b) := by rw [← hright]; exact haway1
  have hucycle : u.SameCycle (reverse a) b :=
    (swap_sameCycle_away v color hcolor a (reverse b) (reverse a) b haway1 haway2).mpr hcycle
  have hsplit : cycleCount v' = cycleCount u + 1 := by
    have h := cycles_card_swap_of_same u hpair hucycle
    simpa only [← hv',cycleCount,Nat.card_eq_fintype_card] using h
  have hnab : a ≠ reverse b := by
    intro h
    apply hpair
    rw [h,hi b]
  have hge : cycleCount v ≤ cycleCount v' := by
    by_cases hc : v.SameCycle a (reverse b)
    · have hh := cycles_card_swap_of_same v hnab hc
      have hh' : cycleCount u = cycleCount v + 1 := by
        simpa only [cycleCount,Nat.card_eq_fintype_card] using hh
      omega
    · have hh : cycleCount u + 1 = cycleCount v := cycleCount_swap_of_not_same v hc
      omega
  have hj : components reverse face = joinPair (components r' face) (reverse a) b :=
    components_conjugate_swap reverse face (sameCycle_mul_le_components reverse face hcycle)
  have hvcolor : ∀ z, color (v' z) = color z := by
    intro z
    rw [hv']
    change color (Equiv.swap (reverse a) b (Equiv.swap a (reverse b) (v z))) = color z
    rw [color_swap color hleft,color_swap color hright,hcolor]
  by_cases hc : components r' face (reverse a) b
  · have hcomp : componentCount reverse face = componentCount r' face := by
      simp only [componentCount,hj,joinPair_eq_of_rel _ hc]
    have hbound := euler_bound r' face
    dsimp [PlanarMap] at hplanar ⊢
    change cycleCount reverse + cycleCount face + cycleCount v =
      Fintype.card A + 2*componentCount reverse face at hplanar
    change cycleCount r' + cycleCount face + cycleCount v' ≤
      Fintype.card A + 2*componentCount r' face at hbound
    change cycleCount r' + cycleCount face + cycleCount v' =
      Fintype.card A + 2*componentCount r' face
    omega
  · have hcomp : componentCount reverse face + 1 = componentCount r' face := by
      simpa only [componentCount,hj] using card_joinPair (components r' face) hc
    have hrab : components r' face a b := by
      have hh : r'.SameCycle a (r' a) :=
        Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' a)
      rw [rePair_apply_a reverse hn hab'] at hh
      exact (show Perm.SameCycle.setoid r' ≤ components r' face from le_sup_left) hh
    have hrAB : components r' face (reverse a) (reverse b) := by
      have hh : r'.SameCycle (reverse a) (r' (reverse a)) :=
        Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' (reverse a))
      rw [rePair_apply_reverse_a reverse hn hab'] at hh
      exact (show Perm.SameCycle.setoid r' ≤ components r' face from le_sup_left) hh
    have hsep : ¬ v'.SameCycle a (reverse b) := by
      intro h
      have hh := sameCycle_mul_le_components r' face h
      exact hc ((components r' face).trans hrAB ((components r' face).trans
        ((components r' face).symm hh) hrab))
    have hawayA : color a ≠ color (reverse a) := by rw [hleft]; exact hab
    have hret1 : Equiv.swap (reverse a) b * v' = u := by
      rw [hv',← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hns : ¬ u.SameCycle a (reverse b) := by
      rw [← hret1]
      exact fun h => hsep ((swap_sameCycle_away v' color hvcolor (reverse a) b a
        (reverse b) hawayA hab).mp h)
    have hret2 : Equiv.swap a (reverse b) * u = v := by
      dsimp [u]
      rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hmerge := cycleCount_swap_of_not_same u hns
    rw [hret2] at hmerge
    dsimp [PlanarMap] at hplanar ⊢
    change cycleCount reverse + cycleCount face + cycleCount v =
      Fintype.card A + 2*componentCount reverse face at hplanar
    change cycleCount r' + cycleCount face + cycleCount v' =
      Fintype.card A + 2*componentCount r' face
    omega

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

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.planar_rePair := @_root_.OAI.Release075.PermCycles.planar_rePair
