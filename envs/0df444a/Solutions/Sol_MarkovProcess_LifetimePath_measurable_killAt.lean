-- Prove2me | solution 1 for MarkovProcess.LifetimePath.measurable_killAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:54:49.610236+00:00
-- url     : https://prove2.me/submissions/29b4bbd8-4fa1-4912-9d0e-205dbeb621d2

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Killing_79b59135
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic killing of lifetime paths

This file truncates a lifetime path at a deterministic finite time. The coordinate at the
killing time itself is the cemetery state, so this operation is distinct from endpoint-retaining
stopping.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {α : Type*} [TopologicalSpace α]





/-- Killing does not change a coordinate strictly before the killing time. -/
theorem coordinate_killAt_of_lt (T t : NNReal) (ω : LifetimePath α)
    (ht : (t : ENNReal) < (T : ENNReal)) :
    coordinate t (killAt T ω) = coordinate t ω := by
  by_cases hω : (t : ENNReal) < ω.lifetime
  · have hk : (t : ENNReal) < min ω.lifetime (T : ENNReal) := lt_min hω ht
    rw [coordinate_of_lt _ _ hk, coordinate_of_lt _ _ hω]
    rfl
  · have hωle : ω.lifetime ≤ (t : ENNReal) := not_lt.mp hω
    rw [coordinate_of_le _ _ hωle]
    apply coordinate_of_le
    exact (min_le_left _ _).trans hωle

/-- At and after the deterministic killing time, the killed coordinate is the cemetery state. -/
@[simp]
theorem coordinate_killAt_of_le (T t : NNReal) (ω : LifetimePath α) (ht : T ≤ t) :
    coordinate t (killAt T ω) = Cemetery.delta := by
  apply coordinate_of_le
  exact (min_le_right _ _).trans (ENNReal.coe_le_coe.mpr ht)



section Measurable

variable [MeasurableSpace α]



end Measurable

end
end MarkovProcess.LifetimePath


open MarkovProcess
open MarkovProcess.LifetimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic killing of lifetime paths

This file truncates a lifetime path at a deterministic finite time. The coordinate at the
killing time itself is the cemetery state, so this operation is distinct from endpoint-retaining
stopping.
-/

open MeasureTheory
open scoped ENNReal



variable {α : Type*} [TopologicalSpace α]












variable [MeasurableSpace α]

namespace MarkovProcess.LifetimePath

end MarkovProcess.LifetimePath
open MarkovProcess.LifetimePath
theorem solution (T : NNReal) :
    Measurable (killAt T : LifetimePath α → LifetimePath α) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpace, MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  apply sup_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_lifetime.min measurable_const).comap_le
  · rw [iSup_le_iff]
    intro t
    rw [MeasurableSpace.comap_comp]
    by_cases ht : (t : ENNReal) < (T : ENNReal)
    · have hfun : coordinate (α := α) t ∘ killAt T = coordinate t := by
        funext ω
        exact coordinate_killAt_of_lt T t ω ht
      rw [hfun]
      exact (measurable_coordinate t).comap_le
    · have hfun : coordinate (α := α) t ∘ killAt T = fun _ ↦ Cemetery.delta := by
        funext ω
        exact coordinate_killAt_of_le T t ω (ENNReal.coe_le_coe.mp (not_lt.mp ht))
      rw [hfun]
      exact measurable_const.comap_le
