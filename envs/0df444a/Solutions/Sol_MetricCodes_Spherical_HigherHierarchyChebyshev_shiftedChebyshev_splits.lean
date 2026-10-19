-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.shiftedChebyshev_splits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/29494348-2ec2-4d2f-a160-a1b336d60a32

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_roots
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_roots

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (shiftedChebyshev R N).Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  rw [shiftedChebyshev_roots hR N, polePolynomial_roots]
  have hscale : 2 / R ≠ (0 : ℝ) := div_ne_zero (by norm_num) hR.ne'
  unfold shiftedChebyshev affinePolynomial
  rw [Polynomial.natDegree_comp, Polynomial.Chebyshev.natDegree_T,
    Polynomial.natDegree_linear hscale]
  simp
end MetricCodes.Spherical.HigherHierarchyChebyshev
