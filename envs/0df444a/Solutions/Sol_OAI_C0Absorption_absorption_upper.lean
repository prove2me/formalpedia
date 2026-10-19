-- Prove2me | solution 1 for OAI.C0Absorption.absorption_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:22:10.409964+00:00
-- url     : https://prove2.me/submissions/9a65bb33-dab7-46fb-88c6-89c1b7332c9e

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators
variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]


theorem solution {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) {LK : ℝ}
    (hLK : 0 ≤ LK) (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y) :
    ∀ x y, dist (absorptionMap Q K x) (absorptionMap Q K y) ≤
      (1+LK * max 1 ‖Q‖) * dist x y := by
  intro x y
  have hQ : dist (Q x.1) (Q y.1) ≤ ‖Q‖ * dist x.1 y.1 := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact Q.le_opNorm _
  have hd1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hm : dist ((x.2, Q x.1) : E × U) (y.2, Q y.1) ≤ max 1 ‖Q‖ * dist x y := by
    rw [Prod.dist_eq]
    apply max_le
    · calc dist x.2 y.2 ≤ 1 * dist x y := by linarith
        _ ≤ max 1 ‖Q‖ * dist x y := by gcongr; exact le_max_left _ _
    · calc dist (Q x.1) (Q y.1) ≤ ‖Q‖ * dist x y := hQ.trans (by gcongr)
        _ ≤ max 1 ‖Q‖ * dist x y := by gcongr; exact le_max_right _ _
  unfold absorptionMap
  calc dist (x.1 + K (x.2, Q x.1)) (y.1 + K (y.2, Q y.1))
      ≤ dist x.1 y.1 + dist (K (x.2, Q x.1)) (K (y.2, Q y.1)) := dist_add_add_le _ _ _ _
    _ ≤ dist x y + LK * (max 1 ‖Q‖ * dist x y) := by
        gcongr
        exact (hK _ _).trans (mul_le_mul_of_nonneg_left hm hLK)
    _ = (1 + LK * max 1 ‖Q‖) * dist x y := by ring

