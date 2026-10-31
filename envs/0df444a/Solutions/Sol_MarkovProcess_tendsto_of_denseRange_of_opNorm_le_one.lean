-- Prove2me | solution 1 for MarkovProcess.tendsto_of_denseRange_of_opNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:31:06.966527+00:00
-- url     : https://prove2.me/submissions/e70f756a-549d-462e-94d1-499e4f565cbf

import Definitions.Def_MarkovProcess_V3H_Semigroup_DenseCoreConvergence_48a35d65
import Mathlib.Analysis.Normed.Operator.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence from a dense core

This module extends pointwise convergence of uniformly contractive continuous
linear maps from the range of a dense map to the whole ambient space.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

namespace MarkovProcess





end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence from a dense core

This module extends pointwise convergence of uniformly contractive continuous
linear maps from the range of a dense map to the whole ambient space.
-/

open Filter Topology


namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution
    {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} (T : ι → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, Tendsto (fun i ↦ T i (D v)) l (nhds (D v))) :
    ∀ f, Tendsto (fun i ↦ T i f) l (nhds f) := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv⟩ := hD.exists_dist_lt f (div_pos hε (by norm_num : (0 : ℝ) < 3))
  have hv' : dist (D v) f < ε / 3 := by
    rw [dist_comm]
    exact hv
  have hcore_eventually : ∀ᶠ i in l, dist (T i (D v)) (D v) < ε / 3 :=
    (Metric.tendsto_nhds.mp (hcore v)) (ε / 3) (div_pos hε (by norm_num))
  filter_upwards [hcore_eventually] with i hi
  have hcontract : dist (T i f) (T i (D v)) ≤ dist f (D v) := by
    calc
      dist (T i f) (T i (D v)) ≤ ‖T i‖ * dist f (D v) := (T i).dist_le_opNorm f (D v)
      _ ≤ 1 * dist f (D v) :=
        mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist f (D v) := one_mul _
  calc
    dist (T i f) f ≤ dist (T i f) (T i (D v)) + dist (T i (D v)) f :=
      dist_triangle _ _ _
    _ ≤ dist (T i f) (T i (D v)) +
        (dist (T i (D v)) (D v) + dist (D v) f) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ ≤ dist f (D v) + (dist (T i (D v)) (D v) + dist (D v) f) :=
      add_le_add hcontract le_rfl
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      exact add_lt_add hv (add_lt_add hi hv')
    _ = ε := by ring
