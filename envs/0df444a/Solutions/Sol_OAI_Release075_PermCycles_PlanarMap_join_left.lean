-- Prove2me | solution 1 for OAI.Release075.PermCycles.PlanarMap.join_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:48:16.719977+00:00
-- url     : https://prove2.me/submissions/73ce09e1-6b90-46d2-a2aa-2c0f4f0e49b4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/RePairing.lean:L66-L79
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.PlanarMap.join_left. The node keeps its source
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

/-- Joining two separate planar components along a chosen cycle slot is planar. -/
theorem PlanarMap.join_left {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : ¬ components f g a b) : PlanarMap (Equiv.swap a b * f) g := by
  have hnf : ¬ f.SameCycle a b := fun h => hab
    ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left) h)
  have hnp : ¬ (f*g).SameCycle a b := fun h => hab (sameCycle_mul_le_components f g h)
  have hc := cycleCount_swap_of_not_same f hnf
  have hd := cycleCount_swap_of_not_same (f*g) hnp
  have hj := components_swap_of_not_same f g hnf
  have hcomp : componentCount (Equiv.swap a b*f) g + 1 = componentCount f g := by
    simpa only [componentCount,hj] using card_joinPair (components f g) hab
  rw [←mul_assoc] at hd
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


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.PlanarMap.join_left := @_root_.OAI.Release075.PermCycles.PlanarMap.join_left
