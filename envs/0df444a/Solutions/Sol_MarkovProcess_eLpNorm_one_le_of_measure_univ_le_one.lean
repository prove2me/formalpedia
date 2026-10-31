-- Prove2me | solution 1 for MarkovProcess.eLpNorm_one_le_of_measure_univ_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:01.661858+00:00
-- url     : https://prove2.me/submissions/e12e2e4c-547c-4eeb-9655-b594cbeadcc9

import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_LpFinite_cf939c30
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]











end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-exponent contraction for sub-Markov kernels

This file proves the scalar subprobability estimate behind contraction of a
sub-Markov kernel on finite `Lᵖ` spaces, and its fibrewise integrated form.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution {ν : Measure α} {f : α → ℝ}
    [IsFiniteMeasure ν] {p : NNReal} (hp : 1 ≤ p) (hν : ν Set.univ ≤ 1)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 1 ν ≤ eLpNorm f p ν := by
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := ν) (f := f) (p := (1 : ℝ≥0∞)) (q := (p : ℝ≥0∞))
    (by exact_mod_cast hp) hf
  calc
    eLpNorm f 1 ν
        ≤ eLpNorm f p ν * ν Set.univ ^ (1 - 1 / (p : ℝ)) := by
          simpa using hcompare
    _ ≤ eLpNorm f p ν * 1 := by
          gcongr
          calc
            ν Set.univ ^ (1 - 1 / (p : ℝ))
                ≤ (1 : ℝ≥0∞) ^ (1 - 1 / (p : ℝ)) := by
                  exact ENNReal.rpow_le_rpow hν (by
                    rw [sub_nonneg, div_le_one (by exact_mod_cast zero_lt_one.trans_le hp)]
                    exact_mod_cast hp)
            _ = 1 := ENNReal.one_rpow _
    _ = eLpNorm f p ν := mul_one _
