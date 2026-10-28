-- Prove2me | solution 1 for Helfgott.mobiusValueGroup000_checked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-28T16:43:45.9843+00:00
-- url     : https://prove2.me/submissions/6f3ce3e6-ba34-40de-8ef3-7d4d5f4d1185

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Theorems.Thm_Helfgott_mobiusValuePair000_checked
import Theorems.Thm_Helfgott_mobiusValuePair001_checked
import Mathlib.Tactic

set_option autoImplicit false

namespace Helfgott

lemma mobiusTreeCheck_join (g : ℕ → ℤ) (B d offset : ℕ) (l r : MobiusCertTree)
    (hl : mobiusTreeCheck g B d offset l = true)
    (hr : mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true) :
    mobiusTreeCheck g B (d + 1) offset (.branch l r) = true := by
  by_cases hoff : B ≤ offset
  · simp [mobiusTreeCheck, hoff]
  · simpa [mobiusTreeCheck, hoff] using And.intro hl hr

end Helfgott

open Helfgott

theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 10 0
    mobiusTableGroup000 = true := by
  unfold mobiusTableGroup000
  exact mobiusTreeCheck_join _ _ _ _ _ _ mobiusValuePair000_checked mobiusValuePair001_checked

#print axioms solution
