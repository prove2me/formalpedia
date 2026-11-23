-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.X_isP0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:54:28.556281+00:00
-- url     : https://prove2.me/submissions/facd8a06-caca-47f2-bb46-7e55d77d71b1

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_isP0_s_ne_zero
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_isP0_s_zero

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) :
    P0Matrix.IsP0Matrix n ((matrixX n k b r s).map (↑· : ℚ → ℝ)) := by
  by_cases hs : s = 0
  · subst hs
    exact X_isP0_s_zero n k b r hn hk hb hrb
  · exact X_isP0_s_ne_zero n k b r s hn hk hb hrb hs
end GroupTheoreticShannonCapacity.Construction
