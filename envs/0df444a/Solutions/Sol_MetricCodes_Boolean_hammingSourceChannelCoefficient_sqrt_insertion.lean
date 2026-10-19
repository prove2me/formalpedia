-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_sqrt_insertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/d57e791f-e1b5-4aa3-bc6d-0f2e6ce11147

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_eq_insertion
import Theorems.Thm_MetricCodes_Boolean_hammingSqrtDivProduct

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : source.val + 1 = target.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt ((n : ℝ) - (k + source.val : ℝ)))⁻¹ *
          Real.sqrt (harmonicCoefficient n k target.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hcoefficient : 0 < harmonicCoefficient n k target.val :=
    harmonicCoefficient_pos (by omega) (by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsreal : 0 < (n : ℝ) - (k + source.val : ℝ) := by
    have hdegree : k + source.val < n := by omega
    exact sub_pos.mpr (by exact_mod_cast hdegree)
  have hnum :
      (((k + source.val : ℕ) : ℝ) - (k : ℝ) + 1) *
          ((n : ℝ) - ((k + source.val : ℕ) : ℝ) - (k : ℝ)) =
        harmonicCoefficient n k target.val := by
    have hval : target.val = source.val + 1 := by omega
    rw [hval]
    simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  rw [hammingSourceChannelCoefficient_eq_insertion
    hn hkL hLn source target hadjacent]
  unfold hammingInsertionChannelSquare
  rw [hnum]
  simpa only [Nat.cast_add] using
    hammingSqrtDivProduct hcoefficient.le hnreal hsreal
end MetricCodes.Boolean
