-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:42:56.083807+00:00
-- url     : https://prove2.me/submissions/d9799d9e-e7e2-4ec8-bdeb-477f986feab6

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_mono

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hd_pos : 0 < d) (hab_eq_cd : (a : ℚ) / b = (c : ℚ) / d) :
    shannonCapacity (fractionGraph a b) = shannonCapacity (fractionGraph c d) :=
  le_antisymm
    (shannonCapacity_fractionGraph_mono a b c d hb_pos (le_of_eq hab_eq_cd))
    (shannonCapacity_fractionGraph_mono c d a b hd_pos (le_of_eq hab_eq_cd.symm))
end GroupTheoreticShannonCapacity
