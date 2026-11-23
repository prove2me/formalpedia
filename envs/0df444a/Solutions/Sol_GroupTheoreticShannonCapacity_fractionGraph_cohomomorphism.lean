-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.fractionGraph_cohomomorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:29.633426+00:00
-- url     : https://prove2.me/submissions/587d12bf-5ae0-4a93-8f96-177f399ac852

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_scalingMap_isCohom

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    ∃ f : ZMod a → ZMod c, ∀ u v, u ≠ v → ¬(fractionGraph a b).Adj u v →
      f u ≠ f v ∧ ¬(fractionGraph c d).Adj (f u) (f v) :=
  ⟨fractionGraph_scalingMap a c, fractionGraph_scalingMap_isCohom a b c d hb_pos hab_le_cd⟩
end GroupTheoreticShannonCapacity
