-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.denom_pos_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:14.500838+00:00
-- url     : https://prove2.me/submissions/f6181464-d3b6-496f-b250-f07c214ee70a

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    0 < (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n := by
  have hb_pos : 0 < (b : ℤ) := by omega
  have hk_pos : 0 < (k : ℤ) := by omega
  have hbn_pos : 0 < (b : ℤ) ^ n := pow_pos hb_pos n
  have h1 : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
  have h2 : 0 < (k : ℤ) * (b : ℤ) ^ n := mul_pos hk_pos hbn_pos
  linarith
end GroupTheoreticShannonCapacity.Construction
