-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_eq_logAtom_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/bf619abd-1e1f-42dc-8bee-442962447f47

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_stabilizer_quadratic_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_eq_log_sum

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
      (∑ i : Fin (r + 1),
        stieltjesLogAtom (quadraticCoordinate (a i)) t) -
        ∑ i : Fin r,
          stieltjesLogAtom (quadraticCoordinate (b i)) t := by
  rw [stieltjesPhase_eq_log_sum h ht, Fin.sum_univ_castSucc]
  have hfactor (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      Real.log ((t + x) / (t + y)) =
        stieltjesLogAtom x t - stieltjesLogAtom y t := by
    unfold stieltjesLogAtom
    rw [Real.log_div (by linarith) (by linarith),
      Real.log_div (by linarith) ht.ne',
      Real.log_div (by linarith) ht.ne']
    ring
  simp_rw [hfactor _ _ (h.ambient_quadratic_nonneg _)
    (h.stabilizer_quadratic_pos _).le]
  unfold stieltjesLogAtom
  rw [Finset.sum_sub_distrib]
  ring
end MetricCodes.Spherical.HigherHierarchy
