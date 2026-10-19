-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.shiftedChebyshev_eq_leadingCoeff_mul_polePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/367257e0-841c-423e-a5bd-4b6975317b54

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_monic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_roots
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_splits
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_splits

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (N : ℕ) :
    shiftedChebyshev R N =
      Polynomial.C (shiftedChebyshev R N).leadingCoeff * polePolynomial R N := by
  calc
    shiftedChebyshev R N =
        Polynomial.C (shiftedChebyshev R N).leadingCoeff *
          ((shiftedChebyshev R N).roots.map
            (fun x => Polynomial.X - Polynomial.C x)).prod :=
      (shiftedChebyshev_splits hR N).eq_prod_roots
    _ = Polynomial.C (shiftedChebyshev R N).leadingCoeff *
          ((polePolynomial R N).roots.map
            (fun x => Polynomial.X - Polynomial.C x)).prod := by
      rw [shiftedChebyshev_roots hR N]
    _ = Polynomial.C (shiftedChebyshev R N).leadingCoeff *
          polePolynomial R N := by
      exact congrArg
        (fun P : Polynomial ℝ =>
          Polynomial.C (shiftedChebyshev R N).leadingCoeff * P)
        ((polePolynomial_splits R N).eq_prod_roots_of_monic
          (polePolynomial_monic R N)).symm
end MetricCodes.Spherical.HigherHierarchyChebyshev
