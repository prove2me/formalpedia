-- Prove2me | solution 1 for MarkovProcess.Semigroup.tendsto_zero_of_nonneg_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:17:08.19199+00:00
-- url     : https://prove2.me/submissions/88577b7f-5b37-4531-99b8-d90813c9e9e5

import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Mathlib.Analysis.SpecificLimits.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess.Semigroup

open Filter Set Topology











end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/


open Filter Set Topology









namespace MarkovProcess.Semigroup

end MarkovProcess.Semigroup
open MarkovProcess.Semigroup
theorem solution {ι : Type*} {l : Filter ι}
    {e r : ι → ℝ}
    (he : ∀ i, 0 ≤ e i)
    (her : ∀ i, (e i) ^ 2 ≤ r i)
    (hr : Tendsto r l (nhds 0)) :
    Tendsto e l (nhds 0) := by
  rw [Metric.tendsto_nhds] at hr ⊢
  intro ε hε
  filter_upwards [hr (ε ^ 2) (sq_pos_of_pos hε)] with i hi
  have he_sq_lt : (e i) ^ 2 < ε ^ 2 := by
    calc
      (e i) ^ 2 ≤ r i := her i
      _ ≤ |r i| := le_abs_self (r i)
      _ = dist (r i) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε ^ 2 := hi
  have he_lt : e i < ε :=
    (sq_lt_sq₀ (he i) hε.le).1 he_sq_lt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he i)]
  exact he_lt
