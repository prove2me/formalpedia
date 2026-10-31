-- Prove2me | solution 1 for MarkovProcess.LifetimePath.lifetime_killAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:54:41.885392+00:00
-- url     : https://prove2.me/submissions/b3152dc1-e231-4f00-88ab-e2dea30039f0

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
@[simp]
theorem solution (T : NNReal) (ω : LifetimePath α) :
    (killAt T ω).lifetime = min ω.lifetime (T : ENNReal) :=
  rfl
