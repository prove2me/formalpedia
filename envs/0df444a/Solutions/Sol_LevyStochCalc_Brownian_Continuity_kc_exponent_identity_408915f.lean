-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_exponent_identity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:37:29.83332+00:00
-- url     : https://prove2.me/submissions/f40c65cd-04aa-4a59-87f1-34901bad1bfd

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc.Brownian.Continuity in
/-- **KC exponent identity.** `2ⁿ · ((1/2)ⁿ)^q / ((1/2)^α)ⁿ)^p = ((1/2)^{q−αp−1})ⁿ`.
Collapses the per-level Borel–Cantelli factor (a `2ⁿ` union over level-`n`
dyadics, each a Markov term `(2^{−n})^q / (2^{−αn})^p`) to a single geometric
ratio `(1/2)^{q−αp−1}`, which is `< 1` exactly when `αp < q − 1`. -/
lemma solution {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  have e1 : ((1 / 2 : ℝ) ^ n) ^ q = (1 / 2 : ℝ) ^ ((n : ℝ) * q) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) n, ← Real.rpow_mul (le_of_lt h2)]
  have e2 : (((1 / 2 : ℝ) ^ α) ^ n) ^ p = (1 / 2 : ℝ) ^ (α * (n : ℝ) * p) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) n, ← Real.rpow_mul (le_of_lt h2),
        ← Real.rpow_mul (le_of_lt h2)]
  have e3 : (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt h2), Real.rpow_natCast,
        show (1 / 2 : ℝ) ^ n = (2 ^ n)⁻¹ from by rw [one_div, inv_pow], inv_inv]
  have e4 : ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n
      = (1 / 2 : ℝ) ^ ((q - α * p - 1) * (n : ℝ)) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (q - α * p - 1)) n,
        ← Real.rpow_mul (le_of_lt h2)]
  rw [e1, e2, e3, e4, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt h2),
      ← Real.rpow_add h2, ← Real.rpow_add h2]
  congr 1
  ring
