-- Prove2me | solution 1 for MarkovProcess.LifetimePath.exitTime_ofContinuousPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:53:31.413477+00:00
-- url     : https://prove2.me/submissions/712aeca2-f5cd-48c0-974d-5c575439c3c4

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
@[simp]
theorem solution (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U (ofContinuousPath omega) = ContinuousPath.exitTime U omega := by
  apply congrArg sInf
  ext s
  constructor
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    intro homega
    apply ht
    exact ⟨omega t, homega, coordinate_ofContinuousPath omega t |>.symm⟩
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    rintro ⟨x, hx, hcoordinate⟩
    rw [coordinate_ofContinuousPath] at hcoordinate
    have heq : omega t = x := Sum.inl.inj hcoordinate.symm
    exact ht (heq.symm ▸ hx)
