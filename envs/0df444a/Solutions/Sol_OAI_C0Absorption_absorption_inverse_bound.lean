-- Prove2me | solution 1 for OAI.C0Absorption.absorption_inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:23:30.185813+00:00
-- url     : https://prove2.me/submissions/ed4a3b45-7ed3-4252-803b-5a9cbab95a8f

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
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    {LK cg : ℝ} (hLK : 0 ≤ LK) (hcg : 0 < cg)
    (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y)
    (hg : ∀ x y, cg * dist x y ≤ dist (g x) (g y))
    (hQK : ∀ x : E × U, Q (K x) = g x-x.2) :
    ∀ x y, dist x y ≤ max (1+LK*‖Q‖/cg) (‖Q‖/cg) *
      dist (absorptionMap Q K x) (absorptionMap Q K y) := by
  intro x y
  set D := dist (absorptionMap Q K x) (absorptionMap Q K y) with hD
  have hD0 : 0 ≤ D := dist_nonneg
  have hQA : ∀ w : Z × E, Q (absorptionMap Q K w) = g (w.2, Q w.1) := by
    intro w
    simp only [absorptionMap, map_add, hQK]
    abel
  have hgp : dist (g (x.2, Q x.1)) (g (y.2, Q y.1)) ≤ ‖Q‖ * D := by
    rw [← hQA, ← hQA, dist_eq_norm, ← map_sub, hD, dist_eq_norm]
    exact Q.le_opNorm _
  have hpq : dist ((x.2, Q x.1) : E × U) (y.2, Q y.1) ≤ ‖Q‖ / cg * D := by
    have := hg (x.2, Q x.1) (y.2, Q y.1)
    rw [div_mul_eq_mul_div, le_div_iff₀ hcg]
    linarith
  have h2 : dist x.2 y.2 ≤ ‖Q‖ / cg * D := by
    refine le_trans ?_ hpq
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h1 : dist x.1 y.1 ≤ (1 + LK * ‖Q‖ / cg) * D := by
    have e : x.1 = absorptionMap Q K x - K (x.2, Q x.1) := by simp [absorptionMap]
    have e' : y.1 = absorptionMap Q K y - K (y.2, Q y.1) := by simp [absorptionMap]
    have hk := hK (x.2, Q x.1) (y.2, Q y.1)
    calc dist x.1 y.1 = dist (absorptionMap Q K x - K (x.2, Q x.1)) (absorptionMap Q K y - K (y.2, Q y.1)) := by
          rw [← e, ← e']
      _ ≤ D + dist (K (x.2, Q x.1)) (K (y.2, Q y.1)) := dist_sub_sub_le _ _ _ _
      _ ≤ D + LK * (‖Q‖ / cg * D) := by
          have := mul_le_mul_of_nonneg_left hpq hLK
          linarith
      _ = (1 + LK * ‖Q‖ / cg) * D := by ring
  rw [Prod.dist_eq]
  apply max_le
  · exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)
  · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hD0)

