-- Prove2me | solution 1 for MarkovProcess.tendsto_shiftedUnitDyadicFloorLimit_of_cauchySeq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:44:56.470463+00:00
-- url     : https://prove2.me/submissions/8bd86c18-4b09-4ddc-9cd5-6d757f42ccc4

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovTimeShift_b20f4218
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Theorems.Thm_MarkovProcess_timeShift_unitDyadicFloorValue_apply

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Nonnegative-rational time shifts

This file translates a dense-time process by a nonnegative rational time.  Translation is an
isometry of `NNRat`, so the Kolmogorov increment condition is preserved with exactly the same
exponents and constant.  The final definitions and identities identify the unit-interval
dyadic samples and canonical limit for the shifted process with samples of the original process
on the interval starting at the shift.

No global path is glued here, and no measurability of the canonical limit or modification-law
assertion is made.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*}











noncomputable section

variable [PseudoMetricSpace E]





variable [CompleteSpace E]



end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Nonnegative-rational time shifts

This file translates a dense-time process by a nonnegative rational time.  Translation is an
isometry of `NNRat`, so the Kolmogorov increment condition is preserved with exactly the same
exponents and constant.  The final definitions and identities identify the unit-interval
dyadic samples and canonical limit for the shifted process with samples of the original process
on the interval starting at the shift.

No global path is glued here, and no measurability of the canonical limit or modification-law
assertion is made.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*}












variable [PseudoMetricSpace E]





variable [CompleteSpace E]

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution
    {k : NNRat} {X : NNRat → Ω → E} {ω : Ω} {t : Set.Icc (0 : ℝ) 1}
    (h : CauchySeq (fun n : ℕ ↦ X (shiftedUnitDyadicFloorValue k n t) ω)) :
    Tendsto (fun n : ℕ ↦ X (shiftedUnitDyadicFloorValue k n t) ω) atTop
      (nhds (shiftedUnitDyadicFloorLimit k X ω t)) := by
  simpa only [shiftedUnitDyadicFloorLimit, timeShift_unitDyadicFloorValue_apply] using
    tendsto_unitDyadicFloorLimit_of_cauchySeq
      (X := timeShift k X) (ω := ω) (t := t) h
