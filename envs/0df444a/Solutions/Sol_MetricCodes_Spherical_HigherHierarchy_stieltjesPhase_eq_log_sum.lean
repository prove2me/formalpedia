-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_eq_log_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/8d2bac4b-bdbb-4c91-996b-7307a855e84b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_stabilizer_quadratic_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_integral_inv_add_eq_log_div

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
    stieltjesPhase a b t =
      Real.log ((t + quadraticCoordinate (a (Fin.last r))) / t) +
        ∑ i : Fin r,
          Real.log ((t + quadraticCoordinate (a i.castSucc)) /
            (t + quadraticCoordinate (b i))) := by
  unfold stieltjesPhase
  rw [integral_inv_add_eq_log_div (by simpa using ht)
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.ambient_quadratic_nonneg (Fin.last r))))]
  simp only [add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_inv_add_eq_log_div
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.stabilizer_quadratic_pos i).le))
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.ambient_quadratic_nonneg i.castSucc)))
end MetricCodes.Spherical.HigherHierarchy
