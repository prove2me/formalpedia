-- Prove2me | solution 1 for MarkovProcess.tsum_dyadicIncrementThreshold_add_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:31:19.308202+00:00
-- url     : https://prove2.me/submissions/9cb42473-764d-4877-b834-716946ff8eca

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicIncrements_eff99a2c
import Definitions.Def_MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

section DyadicIncrementSummability

open scoped ENNReal NNReal










end DyadicIncrementSummability

section DyadicBorelCantelli

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]















end DyadicBorelCantelli

section DyadicIncrementControl

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicIncrementControl

section DyadicThresholdTail

open scoped ENNReal NNReal














end DyadicThresholdTail

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/






open scoped ENNReal NNReal










namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    (∑' k : ℕ, dyadicIncrementThreshold γ (n + k)) ≠ ∞ := by
  rw [tsum_dyadicIncrementThreshold_add]
  apply ENNReal.mul_ne_top
  · exact dyadicIncrementThreshold_ne_top hγ n
  · exact ENNReal.inv_ne_top.mpr
      (tsub_pos_iff_lt.mpr (dyadicIncrementThresholdRatio_lt_one hγ)).ne'
