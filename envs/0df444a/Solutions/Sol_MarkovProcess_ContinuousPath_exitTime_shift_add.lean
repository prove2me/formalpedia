-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exitTime_shift_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:29:19.420185+00:00
-- url     : https://prove2.me/submissions/3ac40cd7-894f-49f7-8d25-41dfb6b56d40

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times under shifts

Path-space identities relating the exit time `ContinuousPath.exitTime U` of an open set to the
shift `ContinuousPath.shift t`, and the measurability of the survival events they generate.

* `exitTime_shift_add`: before the exit time, shifting by `t` subtracts `t` from the exit time,
  `τ(θ_t ω) + t = τ(ω)` whenever `t < τ(ω)`;
* `coe_add_lt_exitTime_iff`: the event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}`, which is
  the Chapman--Kolmogorov identity for the process killed at `τ`;
* `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`,
  `measurable_exitTime`: the survival event `{t < τ}` is measurable for the canonical filtration
  at time `t`, and the exit time is a Borel function on path space.

Nothing here involves a probability law.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

section Shift

variable {alpha : Type*} [PseudoMetricSpace alpha]







end Shift

section Measurable

variable {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]







end Measurable

end MarkovProcess.ContinuousPath


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times under shifts

Path-space identities relating the exit time `ContinuousPath.exitTime U` of an open set to the
shift `ContinuousPath.shift t`, and the measurability of the survival events they generate.

* `exitTime_shift_add`: before the exit time, shifting by `t` subtracts `t` from the exit time,
  `τ(θ_t ω) + t = τ(ω)` whenever `t < τ(ω)`;
* `coe_add_lt_exitTime_iff`: the event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}`, which is
  the Chapman--Kolmogorov identity for the process killed at `τ`;
* `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`,
  `measurable_exitTime`: the survival event `{t < τ}` is measurable for the canonical filtration
  at time `t`, and the exit time is a Borel function on path space.

Nothing here involves a probability law.
-/

open MeasureTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [PseudoMetricSpace alpha]



namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) :
    exitTime U (shift t omega) + t = exitTime U omega := by
  apply le_antisymm
  · rw [le_exitTime_iff]
    intro v hv
    have hle : exitTime U omega ≤ v := exitTime_le_of_notMem U omega v hv
    have htv : t ≤ v := ENNReal.coe_le_coe.mp (ht.trans_le hle).le
    have hbad : shift t omega (v - t) ∉ U := by
      rw [shift_apply, add_tsub_cancel_of_le htv]
      exact hv
    calc exitTime U (shift t omega) + (t : ℝ≥0∞) ≤ ((v - t : NNReal) : ℝ≥0∞) + t :=
          add_le_add (exitTime_le_of_notMem U (shift t omega) (v - t) hbad) le_rfl
      _ = v := by rw [← ENNReal.coe_add, tsub_add_cancel_of_le htv]
  · rw [← tsub_le_iff_right, le_exitTime_iff]
    intro u hu
    have hle : exitTime U omega ≤ ((t + u : NNReal) : ℝ≥0∞) :=
      exitTime_le_of_notMem U omega (t + u) hu
    rw [tsub_le_iff_right, ← ENNReal.coe_add, add_comm]
    exact hle
