-- Prove2me | solution 1 for MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:17:01.043304+00:00
-- url     : https://prove2.me/submissions/d5a7396d-4885-4741-bbe5-c068d4cb470a

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
theorem solution {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i ↦ T i w) l (nhds (Tlim w)))
    (hv : Tendsto v l (nhds w)) :
    Tendsto (fun i ↦ T i (v i)) l (nhds (Tlim w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) hε2,
    Metric.tendsto_nhds.mp hTlim (ε / 2) hε2] with i hvi hTi
  have hcontract : dist (T i (v i)) (T i w) ≤ dist (v i) w := by
    calc
      dist (T i (v i)) (T i w) ≤ ‖T i‖ * dist (v i) w := (T i).dist_le_opNorm _ _
      _ ≤ 1 * dist (v i) w := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist (v i) w := one_mul _
  calc
    dist (T i (v i)) (Tlim w) ≤ dist (T i (v i)) (T i w) + dist (T i w) (Tlim w) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hvi) hTi
    _ = ε := add_halves ε
