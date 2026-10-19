-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.Gamma_eq_midpointAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/46ee8301-b707-4d8e-b22a-79d3110d7296

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_eq_midpoint
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Gamma_eq_average_spectralAtom

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open Filter
open scoped Topology BigOperators
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Gamma
      (ambient R r) (stabilizer R r) =
      midpointAverage (angularAtom R) (r + 1) := by
  rw [Gamma_eq_average_spectralAtom hR]
  unfold midpointAverage
  apply congrArg (fun x : ℝ => x / ((r + 1 : ℕ) : ℝ))
  change
    (∑ i : Fin (r + 1),
      MetricCodes.Spherical.HigherHierarchy.spectralAtom
        (inverseQuadratic (pole R (r + 1) i.val))) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => MetricCodes.Spherical.HigherHierarchy.spectralAtom
      (inverseQuadratic (pole R (r + 1) i))) (r + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold angularAtom angularQuadratic
  congr 2
  unfold pole
  rw [poleAngle_eq_midpoint (Nat.zero_lt_succ r)]
  norm_num [Nat.cast_add, Nat.cast_one]
  left
  congr 1
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
