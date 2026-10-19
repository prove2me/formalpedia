-- Prove2me | solution 1 for OAI.Release075.PermCycles.components_conjugate_swap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:43:34.677588+00:00
-- url     : https://prove2.me/submissions/68d83637-207c-4ebd-93ac-0f75de532cdf

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Planarity.lean:L58-L79
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.components_conjugate_swap. The node keeps its source
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

-- ---- from OAI.GroupTheory.Hyperbolic.Planarity ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem swap_rel (s : Setoid A) {a b : A} (hab : s a b) (z : A) :
    s z (Equiv.swap a b z) := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using s.symm hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem sameCycle_conjugate_swap_le (f : Perm A) (s : Setoid A) {a b : A}
    (hf : Perm.SameCycle.setoid f ≤ s) (hab : s a b) :
    Perm.SameCycle.setoid (Equiv.swap a b * f * Equiv.swap a b) ≤ s := by
  apply sameCycle_le_of_step
  intro z
  exact s.trans (swap_rel s hab z) (s.trans
    (hf (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f _)))
    (swap_rel s hab _))

/-- A local re-pairing can only split off one further component, provided its
slots belonged to the same old component. This includes reconnected slots. -/
theorem components_conjugate_swap (f g : Perm A) {a b : A}
    (hab : components f g a b) :
    components f g = joinPair (components (Equiv.swap a b * f * Equiv.swap a b) g) a b := by
  let f' := Equiv.swap a b * f * Equiv.swap a b
  have hret : Equiv.swap a b * f' * Equiv.swap a b = f := by
    dsimp [f']
    simp only [mul_assoc,Equiv.swap_mul_self,mul_one]
    rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
  have hnew : components f' g ≤ components f g := by
    apply sup_le
    · exact sameCycle_conjugate_swap_le f _ le_sup_left hab
    · exact le_sup_right
  apply le_antisymm
  · let s := joinPair (components f' g) a b
    have hs : components f' g ≤ s := le_joinPair _ a b
    apply sup_le
    · have hh := sameCycle_conjugate_swap_le f' s (le_trans le_sup_left hs) (joinPair_rel _ a b)
      rwa [hret] at hh
    · exact le_trans le_sup_right hs
  · exact joinPair_le hnew hab

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


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.components_conjugate_swap := @_root_.OAI.Release075.PermCycles.components_conjugate_swap
