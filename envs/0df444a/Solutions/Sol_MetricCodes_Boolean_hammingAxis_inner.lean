-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAxis_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/bdfc1bcb-fb19-4960-8cfc-5c236ea8ee68

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_sum_sign_mul_eq_hammingDist

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    (x y : BinaryWord n) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (hammingAxis x) (hammingAxis y) =
        MetricCodes.hammingCorrelation x y := by
  classical
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs :
      Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt hn'.le
  have hsne : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hn').ne'
  calc
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
        (hammingAxis x) (hammingAxis y) =
      ∑ a : Fin n,
        ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
          ((Real.sqrt (n : ℝ))⁻¹ * sign (y a)) := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro a _
        simp [hammingAxis, mul_comm]
    _ = ((Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, sign (x a) * sign (y a)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = ((Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ))⁻¹) *
        ((n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ)) := by
        rw [sum_sign_mul_eq_hammingDist]
    _ = MetricCodes.hammingCorrelation x y := by
        unfold MetricCodes.hammingCorrelation
        field_simp [hsne, hn'.ne'] ; nlinarith [hs]
end MetricCodes.Boolean
