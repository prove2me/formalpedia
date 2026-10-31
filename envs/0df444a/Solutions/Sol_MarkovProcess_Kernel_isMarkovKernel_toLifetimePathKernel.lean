-- Prove2me | solution 1 for MarkovProcess.Kernel.isMarkovKernel_toLifetimePathKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:52:31.249823+00:00
-- url     : https://prove2.me/submissions/3b142409-7c1d-4e24-a837-144be8e89969

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Law_b2011c24
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
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]













end Kernel
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal




variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]







namespace MarkovProcess.Kernel

end MarkovProcess.Kernel
open MarkovProcess.Kernel
theorem solution
    (kappa : Kernel beta (ContinuousPath alpha)) [IsMarkovKernel kappa] :
    IsMarkovKernel (toLifetimePathKernel kappa) := by
  rw [toLifetimePathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
