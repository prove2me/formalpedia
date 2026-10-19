-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.shiftedChebyshev_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/921eb7ea-c9b5-4094-a952-97e6cdaaf00a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_roots

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
    (shiftedChebyshev R N).roots = (polePolynomial R N).roots := by
  have hR' : R ≠ 0 := hR.ne'
  have hscale : 2 / R ≠ (0 : ℝ) := div_ne_zero (by norm_num) hR'
  rw [polePolynomial_roots]
  unfold shiftedChebyshev affinePolynomial
  rw [Polynomial.roots_comp_C_mul_X_add_C _ _ _
    (isUnit_iff_ne_zero.mpr hscale)]
  rw [Polynomial.Chebyshev.roots_T_real]
  have hinj : Set.InjOn
      (fun k : ℕ => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (N : ℝ))))
      (Finset.range N : Set ℕ) := by
    exact (Finset.range N).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_T_real_nodup N)
  rw [Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _hi
  simp only [Function.comp_apply, Ring.inverse_eq_inv]
  change (2 / R)⁻¹ *
      (Real.cos ((2 * (i : ℝ) + 1) * Real.pi / (2 * (N : ℝ))) - -1) =
    pole R N i
  unfold pole poleAngle
  push_cast
  field_simp
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
