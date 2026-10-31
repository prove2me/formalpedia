-- Prove2me | solution 1 for MarkovProcess.LifetimePath.exists_coordinate_eq_alive_of_lt_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:53:24.24325+00:00
-- url     : https://prove2.me/submissions/556a81c4-93c5-48fc-98b0-7756afb2ff82

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
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
# Exit times of lifetime paths

This file defines the first time at which a lifetime path is not a live point of a prescribed
set. Reaching the cemetery state counts as exit. The infimum of the empty set is infinity, so a
path which never exits has infinite exit time.

Only deterministic order properties are proved here. No measurability or stopping-time claim is
made.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]



/-- A failed live-`U` coordinate bounds the first exit time from above. -/
theorem exitTime_le_of_coordinate_notMem (U : Set alpha) (omega : LifetimePath alpha)
    (t : NNReal) (ht : coordinate t omega ∉ Cemetery.alive '' U) :
    exitTime U omega ≤ (t : ENNReal) := by
  apply sInf_le
  exact ⟨t, rfl, ht⟩





end LifetimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]





end LifetimePath

end
end MarkovProcess


open MarkovProcess
open MarkovProcess.LifetimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times of lifetime paths

This file defines the first time at which a lifetime path is not a live point of a prescribed
set. Reaching the cemetery state counts as exit. The infimum of the empty set is infinity, so a
path which never exits has infinite exit time.

Only deterministic order properties are proved here. No measurability or stopping-time claim is
made.
-/

open Set
open scoped ENNReal




variable {alpha : Type*} [TopologicalSpace alpha]





namespace MarkovProcess.LifetimePath

end MarkovProcess.LifetimePath
open MarkovProcess.LifetimePath
theorem solution (U : Set alpha)
    (omega : LifetimePath alpha) (t : NNReal) (ht : (t : ENNReal) < exitTime U omega) :
    ∃ x ∈ U, coordinate t omega = Cemetery.alive x := by
  by_contra hcoordinate
  have hnotmem : coordinate t omega ∉ Cemetery.alive '' U := by
    rintro ⟨x, hx, hxeq⟩
    exact hcoordinate ⟨x, hx, hxeq.symm⟩
  exact (not_le_of_gt ht) (exitTime_le_of_coordinate_notMem U omega t hnotmem)
