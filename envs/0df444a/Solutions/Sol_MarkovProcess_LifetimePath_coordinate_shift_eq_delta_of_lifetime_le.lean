-- Prove2me | solution 1 for MarkovProcess.LifetimePath.coordinate_shift_eq_delta_of_lifetime_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:53:17.011206+00:00
-- url     : https://prove2.me/submissions/0bef217c-cbd9-489a-9c30-6423472db173

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



/-- At and after the shifted lifetime, the shifted coordinate is the cemetery state. -/
@[simp]
theorem coordinate_shift_of_le (S t : NNReal) (ω : LifetimePath α)
    (ht : (shift S ω).lifetime ≤ (t : ENNReal)) :
    coordinate t (shift S ω) = Cemetery.delta :=
  coordinate_of_le _ _ ht



/-- Shifting at or beyond the original lifetime leaves zero remaining lifetime. -/
theorem lifetime_shift_eq_zero_of_le (S : NNReal) (ω : LifetimePath α)
    (hω : ω.lifetime ≤ (S : ENNReal)) : (shift S ω).lifetime = 0 := by
  rw [lifetime_shift]
  exact tsub_eq_zero_iff_le.mpr hω





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













namespace MarkovProcess.LifetimePath

end MarkovProcess.LifetimePath
open MarkovProcess.LifetimePath
theorem solution (S t : NNReal) (ω : LifetimePath α)
    (hω : ω.lifetime ≤ (S : ENNReal)) :
    coordinate t (shift S ω) = Cemetery.delta := by
  apply coordinate_shift_of_le
  rw [lifetime_shift_eq_zero_of_le S ω hω]
  exact bot_le
