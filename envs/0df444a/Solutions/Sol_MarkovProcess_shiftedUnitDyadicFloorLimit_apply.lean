-- Prove2me | solution 1 for MarkovProcess.shiftedUnitDyadicFloorLimit_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:30:52.114396+00:00
-- url     : https://prove2.me/submissions/3a61e69b-9a3a-4b5a-a5fc-de97be0d4ddf

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovTimeShift_b20f4218
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

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



namespace MarkovProcess
end MarkovProcess
open MarkovProcess
@[simp]
theorem solution
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) (t : Set.Icc (0 : ℝ) 1) :
    shiftedUnitDyadicFloorLimit k X ω t = unitDyadicFloorLimit (timeShift k X) ω t :=
  rfl
