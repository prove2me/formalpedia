-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.numer_ne_zero_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:51.131429+00:00
-- url     : https://prove2.me/submissions/97d96d7c-ee0c-40a5-b580-f6a9a250ba77

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_numer_pos_nat

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s) :
    (s : ℤ) ^ n * (r : ℤ) + (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n ≠ 0 :=
  ne_of_gt (numer_pos_nat n k b r s hk hb hs)
end GroupTheoreticShannonCapacity.Construction
