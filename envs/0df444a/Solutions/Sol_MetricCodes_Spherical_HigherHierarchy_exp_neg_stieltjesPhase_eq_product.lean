-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exp_neg_stieltjesPhase_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/44972a32-bd1f-4d26-9f5d-8066ca10620b

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
    Real.exp (-stieltjesPhase a b t) =
      stieltjesPhaseProduct a b t := by
  have hlast : 0 < t + quadraticCoordinate (a (Fin.last r)) := by
    linarith [h.ambient_quadratic_nonneg (Fin.last r)]
  have hambient (i : Fin (r + 1)) :
      0 < t + quadraticCoordinate (a i) := by
    linarith [h.ambient_quadratic_nonneg i]
  have hstabilizer (i : Fin r) :
      0 < t + quadraticCoordinate (b i) := by
    linarith [h.stabilizer_quadratic_pos i]
  have hexp :
      Real.exp (stieltjesPhase a b t) =
        ((t + quadraticCoordinate (a (Fin.last r))) / t) *
          ∏ i : Fin r,
            ((t + quadraticCoordinate (a i.castSucc)) /
              (t + quadraticCoordinate (b i))) := by
    rw [stieltjesPhase_eq_log_sum h ht, Real.exp_add]
    congr 1
    · exact Real.exp_log (div_pos hlast ht)
    · rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      exact Real.exp_log
        (div_pos (hambient i.castSucc) (hstabilizer i))
  rw [Real.exp_neg, hexp]
  unfold stieltjesPhaseProduct
  rw [Finset.prod_div_distrib, Fin.prod_univ_castSucc]
  have hcast :
      0 < ∏ i : Fin r, (t + quadraticCoordinate (a i.castSucc)) :=
    Finset.prod_pos fun i _ => hambient i.castSucc
  have hstabprod :
      0 < ∏ i : Fin r, (t + quadraticCoordinate (b i)) :=
    Finset.prod_pos fun i _ => hstabilizer i
  field_simp [ht.ne', hlast.ne', hcast.ne', hstabprod.ne']
end MetricCodes.Spherical.HigherHierarchy
