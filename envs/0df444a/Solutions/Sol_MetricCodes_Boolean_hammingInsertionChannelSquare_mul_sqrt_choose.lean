-- Prove2me | solution 1 for MetricCodes.Boolean.hammingInsertionChannelSquare_mul_sqrt_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/b6becfb0-6067-4fd9-8446-3272e9903368

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingPositiveRadicalSymmetrization

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k i : ℕ} (hn : 0 < n)
    (_ : k ≤ i) (hboundary : i + k < n) :
    hammingInsertionChannelSquare n k i *
        Real.sqrt (n.choose (i + 1) : ℝ) =
      MetricCodes.hammingJacobiEntry n k i *
        Real.sqrt (n.choose i : ℝ) := by
  have hi : i < n := by omega
  have hd : 0 < (n.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hi)
  have he : 0 < (n.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show i + 1 ≤ n by omega)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) - (i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hi)
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcross :
      (n.choose i : ℝ) * ((n : ℝ) - (i : ℝ)) =
        (n.choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (Nat.choose_succ_right_eq n i)
    simpa [Nat.cast_sub (Nat.le_of_lt hi)] using h.symm
  have hradical := hammingPositiveRadicalSymmetrization
    (r := (((i : ℝ) - (k : ℝ) + 1) *
      ((n : ℝ) - (i : ℝ) - (k : ℝ))))
    he hd hb ha hN hcross.symm
  unfold hammingInsertionChannelSquare MetricCodes.hammingJacobiEntry
  convert hradical using 1 ; ring_nf
end MetricCodes.Boolean
