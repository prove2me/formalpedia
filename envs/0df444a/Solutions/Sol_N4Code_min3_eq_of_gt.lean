-- Prove2me | solution 1 for N4Code.min3_eq_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:04.395646+00:00
-- url     : https://prove2.me/submissions/50f3d2c9-d00c-4cea-8812-62a81c763575

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b c d : ℕ} (ha : d < a) (hc : d < c) (hm : min a (min b c) = d) :
    b = d := by
  have hle : d ≤ b := by
    rw [← hm]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hle' : b ≤ d := by
    by_contra hnot
    have hgt : d < b := lt_of_not_ge hnot
    have hb1 : d + 1 ≤ b := Nat.succ_le_of_lt hgt
    have hb2 : d + 1 ≤ a := Nat.succ_le_of_lt ha
    have hb3 : d + 1 ≤ c := Nat.succ_le_of_lt hc
    have hmin_ge : d + 1 ≤ min a (min b c) := by
      apply le_min hb2
      apply le_min hb1 hb3
    rw [hm] at hmin_ge
    omega
  omega
end N4Code
