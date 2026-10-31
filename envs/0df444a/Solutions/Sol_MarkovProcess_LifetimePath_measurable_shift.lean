-- Prove2me | solution 1 for MarkovProcess.LifetimePath.measurable_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:54:58.96978+00:00
-- url     : https://prove2.me/submissions/d92aae79-1be3-413e-9dd2-15601723af56

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Shift_1241ab85
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
# Deterministic time shifts of lifetime paths

This file shifts a lifetime path forward by a fixed finite time. A shift beyond the original
lifetime produces a path with zero lifetime, hence with cemetery state at every coordinate.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {α : Type*} [TopologicalSpace α]



@[simp]
theorem lifetime_shift (S : NNReal) (ω : LifetimePath α) :
    (shift S ω).lifetime = ω.lifetime - (S : ENNReal) :=
  rfl

/-- A shifted coordinate before the shifted lifetime is the corresponding original coordinate. -/
theorem coordinate_shift_of_lt (S t : NNReal) (ω : LifetimePath α)
    (ht : (t : ENNReal) < (shift S ω).lifetime) :
    coordinate t (shift S ω) = coordinate (S + t) ω := by
  rw [coordinate_of_lt _ _ ht]
  have hst : ((S + t : NNReal) : ENNReal) < ω.lifetime := by
    rw [ENNReal.coe_add, add_comm]
    exact lt_tsub_iff_right.mp ht
  rw [coordinate_of_lt _ _ hst]
  rfl

/-- At and after the shifted lifetime, the shifted coordinate is the cemetery state. -/
@[simp]
theorem coordinate_shift_of_le (S t : NNReal) (ω : LifetimePath α)
    (ht : (shift S ω).lifetime ≤ (t : ENNReal)) :
    coordinate t (shift S ω) = Cemetery.delta :=
  coordinate_of_le _ _ ht

/-- Every shifted coordinate is the corresponding original coordinate, including at and after
the lifetime, where both sides are the cemetery state. -/
@[simp]
theorem coordinate_shift (S t : NNReal) (ω : LifetimePath α) :
    coordinate t (shift S ω) = coordinate (S + t) ω := by
  by_cases ht : (t : ENNReal) < (shift S ω).lifetime
  · exact coordinate_shift_of_lt S t ω ht
  · rw [coordinate_shift_of_le S t ω (not_lt.mp ht)]
    apply Eq.symm
    apply coordinate_of_le
    rw [lifetime_shift] at ht
    rw [ENNReal.coe_add, add_comm]
    exact not_lt.mp (lt_tsub_iff_right.not.mp ht)







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
# Deterministic time shifts of lifetime paths

This file shifts a lifetime path forward by a fixed finite time. A shift beyond the original
lifetime produces a path with zero lifetime, hence with cemetery state at every coordinate.
-/

open MeasureTheory
open scoped ENNReal



variable {α : Type*} [TopologicalSpace α]


















variable [MeasurableSpace α]

namespace MarkovProcess.LifetimePath

end MarkovProcess.LifetimePath
open MarkovProcess.LifetimePath
theorem solution (S : NNReal) :
    Measurable (shift S : LifetimePath α → LifetimePath α) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpace, MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  apply sup_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_lifetime.sub measurable_const).comap_le
  · rw [iSup_le_iff]
    intro t
    rw [MeasurableSpace.comap_comp]
    have hfun : coordinate (α := α) t ∘ shift S = coordinate (S + t) := by
      funext ω
      exact coordinate_shift S t ω
    rw [hfun]
    exact (measurable_coordinate (S + t)).comap_le
