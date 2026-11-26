-- Prove2me | solution 1 for N4Code.min3_le_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:45.249156+00:00
-- url     : https://prove2.me/submissions/34a6c258-ef22-4313-a968-f0c8fb484395

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b c d : ℕ} (ha : d < a) (hc : d < c) (hm : min a (min b c) ≤ d) :
    b ≤ d := by
  have hle : min b c ≤ d := by
    by_contra hnot
    have hgt : d < min b c := lt_of_not_ge hnot
    have hb1 : d + 1 ≤ min b c := Nat.succ_le_of_lt hgt
    have hb2 : d + 1 ≤ a := Nat.succ_le_of_lt ha
    have hmin_ge : d + 1 ≤ min a (min b c) := by
      apply le_min hb2 hb1
    omega
  rcases (min_le_iff.mp hle) with hb | hc'
  · exact hb
  · exfalso
    omega
end N4Code
