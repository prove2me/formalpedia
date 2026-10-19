-- Prove2me | solution 1 for MetricCodes.sum_booleanHarmonicDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/d516172e-1f09-4aeb-b1fc-2de6de6a8dfe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators InnerProductSpace
namespace MetricCodes
theorem _root_.solution (n L : ℕ) (hL : 2 * L ≤ n) :
    (∑ k ∈ Finset.range (L + 1), booleanHarmonicDimension n k) =
      n.choose L := by
  induction L generalizing n with
  | zero =>
      simp [booleanHarmonicDimension]
  | succ L ih =>
      have hprev : 2 * L ≤ n := by omega
      have hhalf : L < n / 2 := by omega
      have hmono : n.choose L ≤ n.choose (L + 1) :=
        Nat.choose_le_succ_of_lt_half_left hhalf
      rw [Finset.sum_range_succ, ih n hprev]
      change n.choose L + (n.choose (L + 1) - n.choose L) =
        n.choose (L + 1)
      omega
end MetricCodes
