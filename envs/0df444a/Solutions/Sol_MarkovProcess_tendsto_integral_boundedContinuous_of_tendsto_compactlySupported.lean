-- Prove2me | solution 1 for MarkovProcess.tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:44:48.769713+00:00
-- url     : https://prove2.me/submissions/d62fb5b9-e764-4e21-9b2b-0ae62db93ad3

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_abs_integral_sub_integral_smul_le
import Theorems.Thm_MarkovProcess_exists_compactlySupported_one_sub_lt_integral

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
theorem solution
    [PseudoEMetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]
    [LocallyCompactSpace X] [T2Space X] {iota : Type*} {l : Filter iota}
    (mu : iota → Measure X) (nu : Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [IsProbabilityMeasure nu]
    (h : ∀ g : C_c(X, ℝ), Tendsto (fun i ↦ ∫ y, g y ∂mu i) l (nhds (∫ y, g y ∂nu)))
    (f : X →ᵇ ℝ) : Tendsto (fun i ↦ ∫ y, f y ∂mu i) l (nhds (∫ y, f y ∂nu)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hnorm : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hdpos : 0 < eps / (3 * (‖f‖ + 1)) := by positivity
  obtain ⟨g, hg01, hgint⟩ := exists_compactlySupported_one_sub_lt_integral nu hdpos
  have hsmall : ‖f‖ * (eps / (3 * (‖f‖ + 1))) ≤ eps / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    have hexpand : eps * (3 * (‖f‖ + 1)) - ‖f‖ * eps * 3 = 3 * eps := by ring
    linarith only [hexpand, heps]
  have htrunc : ∀ᶠ i in l,
      |(∫ y, (f • g) y ∂mu i) - ∫ y, (f • g) y ∂nu| < eps / 3 := by
    have hstep := Metric.tendsto_nhds.mp (h (f • g)) (eps / 3) (by positivity)
    simpa only [Real.dist_eq] using hstep
  have hmass : ∀ᶠ i in l, 1 - (∫ y, g y ∂mu i) < eps / (3 * (‖f‖ + 1)) :=
    Tendsto.eventually_lt_const (by linarith only [hgint])
      (tendsto_const_nhds.sub (h g))
  filter_upwards [htrunc, hmass] with i hitrunc himass
  rw [Real.dist_eq]
  have hkey := abs_integral_sub_integral_smul_le (mu i) f g hg01
  have hkey0 := abs_integral_sub_integral_smul_le nu f g hg01
  have hbound : ‖f‖ * (1 - ∫ y, g y ∂mu i) ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left himass.le hnorm
  have hbound0 : ‖f‖ * (1 - ∫ y, g y ∂nu) ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith only [hgint]) hnorm
  have htri := abs_sub_le (∫ y, f y ∂mu i) (∫ y, (f • g) y ∂mu i) (∫ y, f y ∂nu)
  have htri0 := abs_sub_le (∫ y, (f • g) y ∂mu i) (∫ y, (f • g) y ∂nu) (∫ y, f y ∂nu)
  have hcomm := abs_sub_comm (∫ y, (f • g) y ∂nu) (∫ y, f y ∂nu)
  linarith only [hkey, hkey0, hitrunc, hbound, hbound0, hsmall, htri, htri0, hcomm]
