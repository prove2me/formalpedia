-- Prove2me | solution 1 for MarkovProcess.PositiveC0OperatorMeasure.functional_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:09:24.420613+00:00
-- url     : https://prove2.me/submissions/b42998df-1a81-4fe9-9c80-c339bf697cb9

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess

variable {α : Type*} [TopologicalSpace α]





namespace PositiveC0OperatorMeasure









variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)





variable [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]









end PositiveC0OperatorMeasure

end MarkovProcess


open MarkovProcess
open MarkovProcess.PositiveC0OperatorMeasure
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty


variable {α : Type*} [TopologicalSpace α]














variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)



namespace MarkovProcess.PositiveC0OperatorMeasure
end MarkovProcess.PositiveC0OperatorMeasure
open MarkovProcess.PositiveC0OperatorMeasure
@[simp]
theorem solution (x : α) (f : C_c(α, ℝ)) :
    functional T hT x f = T (compactlySupportedToC0LinearMap f) x :=
  rfl
