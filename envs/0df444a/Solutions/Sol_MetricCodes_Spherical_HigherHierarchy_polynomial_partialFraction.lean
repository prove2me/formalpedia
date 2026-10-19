-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.polynomial_partialFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/9d4dd455-b515-4c5a-801a-26a0bfcab076

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    {x : Fin (r + 1) → ℝ} (hx : Function.Injective x)
    (P : Polynomial ℝ)
    (hdegree : P.degree <
      (Finset.univ : Finset (Fin (r + 1))).card)
    {z : ℝ} (hz : ∀ i : Fin (r + 1), z ≠ x i) :
    P.eval z / (∏ i : Fin (r + 1), (z - x i)) =
      ∑ i : Fin (r + 1),
        (P.eval (x i) /
          (∏ j ∈ Finset.univ.erase i, (x i - x j))) /
            (z - x i) := by
  classical
  have hinterpolate :
      P = Lagrange.interpolate
        (Finset.univ : Finset (Fin (r + 1))) x
        (fun i => P.eval (x i)) :=
    Lagrange.eq_interpolate hx.injOn hdegree
  have hvalue := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := x) (x := z)
    (fun i => P.eval (x i))
    (fun i _ => hz i)
  rw [← hinterpolate] at hvalue
  have hprod : (∏ i : Fin (r + 1), (z - x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact sub_ne_zero.mpr (hz i)
  have hnodal :
      (Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 1))) x).eval z =
          ∏ i : Fin (r + 1), (z - x i) := by
    simp [Lagrange.nodal, Polynomial.eval_prod]
  rw [hnodal] at hvalue
  rw [hvalue, mul_div_cancel_left₀ _ hprod]
  apply Finset.sum_congr rfl
  intro i _
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib]
  ring
end MetricCodes.Spherical.HigherHierarchy
