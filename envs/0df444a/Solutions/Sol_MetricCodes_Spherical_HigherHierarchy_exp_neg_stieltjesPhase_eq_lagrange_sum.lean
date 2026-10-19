-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exp_neg_stieltjesPhase_eq_lagrange_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/c435d1db-b875-4452-9f7d-e7d2dc7c1ca9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exp_neg_stieltjesPhase_eq_product
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPartialFraction

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    Real.exp (-stieltjesPhase a b t) =
      ∑ i : Fin (r + 1),
        lagrangeWeight a b i *
          (t / (t + quadraticCoordinate (a i))) := by
  rw [exp_neg_stieltjesPhase_eq_product h ht]
  unfold stieltjesPhaseProduct
  rw [show t * (∏ i : Fin r, (t + quadraticCoordinate (b i))) /
      (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i))) =
        t * ((∏ i : Fin r, (t + quadraticCoordinate (b i))) /
          (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i)))) by ring]
  rw [stieltjesPartialFraction h ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end MetricCodes.Spherical.HigherHierarchy
