-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_sqrt_deletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/1ffdfc4d-452b-4f3e-a821-d3e4315e86b1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_eq_deletion
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
    (hadjacent : target.val + 1 = source.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt (k + source.val : ℝ))⁻¹ *
          Real.sqrt (harmonicCoefficient n k source.val) := by
  have hs := source.isLt
  have hcoefficient : 0 < harmonicCoefficient n k source.val :=
    harmonicCoefficient_pos (by omega) (by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsreal : 0 < (k + source.val : ℝ) := by
    exact_mod_cast (show 0 < k + source.val by omega)
  have hnum :
      (((k + target.val : ℕ) : ℝ) - (k : ℝ) + 1) *
          ((n : ℝ) - ((k + target.val : ℕ) : ℝ) - (k : ℝ)) =
        harmonicCoefficient n k source.val := by
    have hval : source.val = target.val + 1 := by omega
    rw [hval]
    simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  have hden :
      ((k + target.val : ℕ) : ℝ) + 1 =
        ((k + source.val : ℕ) : ℝ) := by
    exact_mod_cast (show k + target.val + 1 = k + source.val by omega)
  rw [hammingSourceChannelCoefficient_eq_deletion
    hn hkL hLn source target hadjacent]
  unfold hammingDeletionChannelSquare
  rw [hnum, hden]
  simpa only [Nat.cast_add] using
    hammingSqrtDivProduct hcoefficient.le hnreal hsreal
end MetricCodes.Boolean
