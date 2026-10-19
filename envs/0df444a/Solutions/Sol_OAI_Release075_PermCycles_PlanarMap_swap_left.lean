-- Prove2me | solution 1 for OAI.Release075.PermCycles.PlanarMap.swap_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:46:47.949088+00:00
-- url     : https://prove2.me/submissions/d3111be1-baa0-4fd0-8fdf-59205d1fdd7f

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/RePairing.lean:L24-L60
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.PlanarMap.swap_left. The node keeps its source
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

-- ---- from OAI.GroupTheory.Hyperbolic.RePairing ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Cutting a cycle does not create positive genus. The component split is proved,
not presumed from a drawing. -/
theorem PlanarMap.swap_left {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : f.SameCycle a b) : PlanarMap (Equiv.swap a b * f) g := by
  by_cases he : a = b
  · subst b
    rw [Equiv.swap_self]
    change PlanarMap (1*f) g
    rwa [one_mul]
  let f' := Equiv.swap a b * f
  have hc : cycleCount f' = cycleCount f + 1 := by
    simpa only [cycleCount,Nat.card_eq_fintype_card] using cycles_card_swap_of_same f he hab
  have hns : ¬ f'.SameCycle a b := swap_splits f he hab
  have hret : Equiv.swap a b * f' = f := by
    dsimp [f']; rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  have hj : components f g = joinPair (components f' g) a b := by
    have h := components_swap_of_not_same f' g hns
    rwa [hret] at h
  have hprod : Equiv.swap a b * (f'*g) = f*g := by rw [←mul_assoc,hret]
  by_cases hrel : components f' g a b
  · have hcomp : componentCount f g = componentCount f' g := by
      simp only [componentCount,hj,joinPair_eq_of_rel _ hrel]
    have hb := euler_bound f' g
    have hh := cycleCount_swap_le (f'*g) a b
    rw [hprod] at hh
    change PlanarMap f' g
    dsimp [PlanarMap] at hp ⊢
    omega
  · have hcomp : componentCount f g + 1 = componentCount f' g := by
      simpa only [componentCount,hj] using card_joinPair (components f' g) hrel
    have hh : cycleCount (f*g) + 1 = cycleCount (f'*g) := by
      have h := cycleCount_swap_of_not_same (f'*g)
        (fun h => hrel (sameCycle_mul_le_components f' g h))
      rwa [hprod] at h
    change PlanarMap f' g
    dsimp [PlanarMap] at hp ⊢
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


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.PlanarMap.swap_left := @_root_.OAI.Release075.PermCycles.PlanarMap.swap_left
