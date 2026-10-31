-- Prove2me | solution 1 for MarkovProcess.Semigroup.tendsto_apply_comp_of_opNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:16:54.863787+00:00
-- url     : https://prove2.me/submissions/e13361cc-6f54-48e0-9e9d-16984ec9b857

import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Analysis.Normed.Operator.Completeness

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong operator limits of contractions

This module constructs the pointwise limit of a sequence of continuous linear
contractions on a complete real normed space and records the small convergence
API needed to pass algebraic identities to the limit.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Completeness

variable [CompleteSpace E]









end Completeness





end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong operator limits of contractions

This module constructs the pointwise limit of a sequence of continuous linear
contractions on a complete real normed space and records the small convergence
API needed to pass algebraic identities to the limit.
-/

open Filter Topology


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




namespace MarkovProcess.Semigroup

end MarkovProcess.Semigroup
open MarkovProcess.Semigroup
theorem solution
    (T U : ℕ → E →L[ℝ] E) (Tlim Ulim : E →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hTlim : ∀ x, Tendsto (fun n ↦ T n x) atTop (nhds (Tlim x)))
    (hUlim : ∀ x, Tendsto (fun n ↦ U n x) atTop (nhds (Ulim x))) (x : E) :
    Tendsto (fun n ↦ T n (U n x)) atTop (nhds (Tlim (Ulim x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hU_eventually : ∀ᶠ n in atTop, dist (U n x) (Ulim x) < ε / 2 :=
    Metric.tendsto_nhds.mp (hUlim x) (ε / 2) hε2
  have hT_eventually : ∀ᶠ n in atTop, dist (T n (Ulim x)) (Tlim (Ulim x)) < ε / 2 :=
    Metric.tendsto_nhds.mp (hTlim (Ulim x)) (ε / 2) hε2
  filter_upwards [hU_eventually, hT_eventually] with n hUn hTn
  have hcontract : dist (T n (U n x)) (T n (Ulim x)) ≤ dist (U n x) (Ulim x) := by
    calc
      dist (T n (U n x)) (T n (Ulim x)) ≤ ‖T n‖ * dist (U n x) (Ulim x) :=
        (T n).dist_le_opNorm (U n x) (Ulim x)
      _ ≤ 1 * dist (U n x) (Ulim x) :=
        mul_le_mul_of_nonneg_right (hT n) dist_nonneg
      _ = dist (U n x) (Ulim x) := one_mul _
  calc
    dist (T n (U n x)) (Tlim (Ulim x)) ≤
        dist (T n (U n x)) (T n (Ulim x)) +
          dist (T n (Ulim x)) (Tlim (Ulim x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      lt_of_le_of_lt (add_le_add hcontract le_rfl) (add_lt_add hUn hTn)
    _ = ε := add_halves ε
