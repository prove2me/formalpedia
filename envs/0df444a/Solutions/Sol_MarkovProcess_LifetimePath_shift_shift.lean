-- Prove2me | solution 1 for MarkovProcess.LifetimePath.shift_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:08.986035+00:00
-- url     : https://prove2.me/submissions/c9a432bc-e57a-421f-8393-09b5d5ed5cae

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Shift_1241ab85
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Theorems.Thm_MarkovProcess_LifetimePath_ext_coordinate

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
theorem solution (S T : NNReal) (ω : LifetimePath α) :
    shift T (shift S ω) = shift (S + T) ω := by
  have hlifetime :
      (shift T (shift S ω)).lifetime = (shift (S + T) ω).lifetime := by
    simp only [lifetime_shift, ENNReal.coe_add]
    exact tsub_tsub ω.lifetime (S : ENNReal) (T : ENNReal)
  apply ext_coordinate
  · exact hlifetime
  · intro t
    by_cases ht : (t : ENNReal) < (shift T (shift S ω)).lifetime
    · rw [coordinate_shift_of_lt T t (shift S ω) ht]
      have hTt : ((T + t : NNReal) : ENNReal) < (shift S ω).lifetime := by
        rw [lifetime_shift] at ht
        rw [ENNReal.coe_add, add_comm]
        exact lt_tsub_iff_right.mp ht
      rw [coordinate_shift_of_lt S (T + t) ω hTt]
      have hsum : (t : ENNReal) < (shift (S + T) ω).lifetime := by
        rwa [← hlifetime]
      rw [coordinate_shift_of_lt (S + T) t ω hsum]
      rw [add_assoc]
    · have htle : (shift T (shift S ω)).lifetime ≤ (t : ENNReal) := not_lt.mp ht
      rw [coordinate_shift_of_le T t (shift S ω) htle]
      rw [coordinate_shift_of_le]
      rwa [← hlifetime]
