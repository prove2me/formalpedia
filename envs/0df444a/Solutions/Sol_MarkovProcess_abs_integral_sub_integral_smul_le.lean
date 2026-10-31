-- Prove2me | solution 1 for MarkovProcess.abs_integral_sub_integral_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:47:07.964567+00:00
-- url     : https://prove2.me/submissions/90136c40-4b98-4fc1-b2d1-938c43025370

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported

namespace MarkovProcess

variable {X : Type*} [MeasurableSpace X]







end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Vague convergence to a probability measure is weak convergence

On a locally compact Polish space, a family of probability measures whose integrals of every
compactly supported continuous test converge to those of a probability measure also converges
against every bounded continuous test.  The reason is that no mass escapes: the limit is a
probability measure, so it is tight, and a compactly supported cutoff with values in `[0, 1]`
captures all but `epsilon` of its mass; convergence of the cutoff integral then forces the
approximating measures to keep all but `epsilon` of their mass on the same compact set, and the
truncation error of a bounded continuous test is at most its norm times the discarded mass.

Main results: `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported`.

Nothing is asserted for families that are not probability measures: for sub-probability measures
the conclusion is false, since mass may escape to infinity.
-/

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported


variable {X : Type*} [MeasurableSpace X]



namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution [TopologicalSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X →ᵇ ℝ) (g : C_c(X, ℝ))
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ y, f y ∂mu) - ∫ y, (f • g) y ∂mu| ≤ ‖f‖ * (1 - ∫ y, g y ∂mu) := by
  have hf : Integrable (fun y ↦ f y) mu := f.integrable mu
  have hg : Integrable (fun y ↦ g y) mu :=
    (map_continuous g).integrable_of_hasCompactSupport g.hasCompactSupport
  have hfg : Integrable (fun y ↦ (f • g) y) mu :=
    (map_continuous (f • g)).integrable_of_hasCompactSupport
      (f • g : C_c(X, ℝ)).hasCompactSupport
  have hbound : ∀ y, ‖f y - (f • g) y‖ ≤ ‖f‖ * (1 - g y) := by
    intro y
    have hy1 : g y ≤ 1 := (hg01 y).2
    have hsub : f y - (f • g) y = f y * (1 - g y) := by
      simp only [CompactlySupportedContinuousMap.smulc_apply, smul_eq_mul]
      ring
    rw [hsub, norm_mul, Real.norm_eq_abs (1 - g y), abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm y) (by linarith)
  have hmaj : Integrable (fun y ↦ ‖f‖ * (1 - g y)) mu :=
    ((integrable_const (1 : ℝ)).sub hg).const_mul ‖f‖
  rw [← integral_sub hf hfg, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hg, integral_const,
    probReal_univ, smul_eq_mul, mul_one]
