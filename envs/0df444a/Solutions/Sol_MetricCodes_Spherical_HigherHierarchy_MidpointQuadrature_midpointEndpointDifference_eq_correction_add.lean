-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.midpointEndpointDifference_eq_correction_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/9334c245-eb80-4734-80a3-5aa3d3b2125b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Set
open scoped Topology BigOperators
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
namespace MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
theorem _root_.solution
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) :
    midpointEndpointDifference f N =
      midpointCorrection f N + (f 0 + f 1) / 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hshift : ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), f ((i : ℝ) / N)) =
        f 0 + ∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / N) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
  have hleft :
      (∑ i ∈ Finset.range N, f ((i : ℝ) / N)) =
        f 0 + ∑ i ∈ Finset.range (N - 1), f (((i : ℝ) + 1) / N) := by
    simpa [hpred] using hshift (N - 1)
  have hright :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) =
        (∑ i ∈ Finset.range (N - 1), f (((i : ℝ) + 1) / N)) + f 1 := by
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      exact_mod_cast hpred
    have hsum := Finset.sum_range_succ
      (fun i : ℕ => f (((i : ℝ) + 1) / N)) (N - 1)
    simpa [hpred, Nat.cast_add, Nat.cast_one, hcast, hN'] using hsum
  unfold midpointEndpointDifference midpointCorrection
  rw [Finset.sum_sub_distrib]
  have hsplit :
      (∑ i ∈ Finset.range N,
        (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2) =
        ((∑ i ∈ Finset.range N, f ((i : ℝ) / N)) +
          (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N))) / 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hsplit, hleft, hright]
  ring
end MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
