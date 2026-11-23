-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.denom_ne_zero_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:26.750384+00:00
-- url     : https://prove2.me/submissions/120d74ee-8f0f-40e2-9b5a-341e8d40521a

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_denom_pos_nat

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0 :=
  ne_of_gt (denom_pos_nat n k b r hk hb)
end GroupTheoreticShannonCapacity.Construction
