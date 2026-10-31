-- Prove2me | solution 1 for MarkovProcess.LifetimePath.killAt_killAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:01.976988+00:00
-- url     : https://prove2.me/submissions/a7335bea-cd00-45e7-bfe0-1762316b2c11

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Killing_79b59135
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Theorems.Thm_MarkovProcess_LifetimePath_ext_coordinate
import Theorems.Thm_MarkovProcess_LifetimePath_lifetime_killAt

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









namespace MarkovProcess.LifetimePath

end MarkovProcess.LifetimePath
open MarkovProcess.LifetimePath
theorem solution (S T : NNReal) (ω : LifetimePath α) :
    killAt T (killAt S ω) = killAt (min T S) ω := by
  apply ext_coordinate
  · simp only [lifetime_killAt, ENNReal.coe_min]
    rw [min_assoc]
    exact congrArg (min ω.lifetime) (min_comm (S : ENNReal) (T : ENNReal))
  · intro t
    by_cases htT : t < T
    · rw [coordinate_killAt_of_lt T t (killAt S ω) (ENNReal.coe_lt_coe.mpr htT)]
      by_cases htS : t < S
      · rw [coordinate_killAt_of_lt S t ω (ENNReal.coe_lt_coe.mpr htS)]
        rw [coordinate_killAt_of_lt (min T S) t ω]
        exact ENNReal.coe_lt_coe.mpr (lt_min htT htS)
      · rw [coordinate_killAt_of_le S t ω (not_lt.mp htS)]
        rw [coordinate_killAt_of_le (min T S) t ω]
        exact (min_le_right T S).trans (not_lt.mp htS)
    · rw [coordinate_killAt_of_le T t (killAt S ω) (not_lt.mp htT)]
      rw [coordinate_killAt_of_le (min T S) t ω]
      exact (min_le_left T S).trans (not_lt.mp htT)
