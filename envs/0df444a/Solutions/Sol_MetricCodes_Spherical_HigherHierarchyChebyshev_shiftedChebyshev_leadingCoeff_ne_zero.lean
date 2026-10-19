-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.shiftedChebyshev_leadingCoeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/5f26312d-618f-4160-bb6a-85aea316648d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_roots
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_roots
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_splits

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    {N : ℕ} (hN : 0 < N) :
    (shiftedChebyshev R N).leadingCoeff ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro hzero
  have hcard := (shiftedChebyshev_splits hR N).natDegree_eq_card_roots
  rw [shiftedChebyshev_roots hR N, polePolynomial_roots] at hcard
  simp at hcard
  simp [hzero] at hcard
  omega
end MetricCodes.Spherical.HigherHierarchyChebyshev
