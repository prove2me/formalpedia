-- Prove2me | solution 1 for MarkovProcess.Cemetery.isOpen_singleton_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:37:56.554562+00:00
-- url     : https://prove2.me/submissions/579305a4-4671-4ef5-b3b7-adb407aced66

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*}









namespace Kernel

variable [MeasurableSpace α]























end Kernel

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*}







namespace MarkovProcess.Cemetery

end MarkovProcess.Cemetery
open MarkovProcess.Cemetery
theorem solution [TopologicalSpace α] :
    IsOpen ({Cemetery.delta} : Set (Cemetery α)) := by
  simpa only [Cemetery.delta, Set.range_unique] using
    (isOpen_range_inr : IsOpen (Set.range (Sum.inr : Unit → α ⊕ Unit)))
