-- Prove2me | solution 1 for OAI.KervaireRibbon.planar_vertex_split_separates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:59:31.418055+00:00
-- url     : https://prove2.me/submissions/e8db30b9-e59f-4396-b2da-1284a8b440a0

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]
theorem solution (σ θ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) (hφ : (σ*θ).SameCycle x y) (hp : planar σ θ) :
    ¬ components (swap x y * σ) θ x y := by
  intro hc
  let r := components (swap x y * σ) θ
  have hr : joinPair r x y = components σ θ := by
    dsimp [r]
    rw [components_swap_sup]
    exact joinPair_eq (components σ θ) ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) hxy)
  have hv := numCycles_swap_split σ hne hxy
  have hre : r = components σ θ := (joinPair_eq r hc).symm.trans hr
  have hi := euler_inequality (swap x y * σ) θ
  change _ ≤ _ + 2*classes r at hi
  rw [hre, hv, mul_assoc] at hi
  have hn := numCycles_swap_split (σ*θ) hne hφ
  unfold planar at hp
  omega

