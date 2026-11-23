-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:55.525427+00:00
-- url     : https://prove2.me/submissions/60985294-f6ef-4dcb-b846-73c215157f1d

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_cohomomorphism
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_le_of_cohomomorphism


set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    shannonCapacity (fractionGraph a b) ≤ shannonCapacity (fractionGraph c d) :=
  let ⟨f, hf⟩ := fractionGraph_cohomomorphism a b c d hb_pos hab_le_cd
  shannonCapacity_le_of_cohomomorphism _ _ f hf
end GroupTheoreticShannonCapacity
