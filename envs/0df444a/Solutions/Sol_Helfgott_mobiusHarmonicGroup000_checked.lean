-- Prove2me | solution 1 for Helfgott.mobiusHarmonicGroup000_checked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-28T16:43:46.725178+00:00
-- url     : https://prove2.me/submissions/656a7659-bf30-447e-9588-783265a516ff

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
import Theorems.Thm_Helfgott_mobiusHarmonicPair000_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair001_checked
import Mathlib.Tactic

set_option autoImplicit false

namespace Helfgott

lemma mobiusHarmonicTreeCheck_join (g M : ℕ → ℤ) (Q B d offset upper : ℕ)
    (l r : MobiusHarmonicTree) (hoff : offset < B)
    (hl : mobiusHarmonicTreeCheck g M Q B d offset l = true)
    (hr : mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true)
    (hu : upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r) :
    mobiusHarmonicTreeCheck g M Q B (d + 1) offset (.branch upper l r) = true := by
  have hoff' : ¬B ≤ offset := not_le.mpr hoff
  simpa [mobiusHarmonicTreeCheck, hoff', Bool.and_assoc, and_assoc] using ⟨hl, hr, hu⟩

end Helfgott

open Helfgott

theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001)
    (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 10 0
    mobiusHarmonicGroup000 = true := by
  unfold mobiusHarmonicGroup000
  refine mobiusHarmonicTreeCheck_join _ _ _ _ _ _ _ _ _ (by norm_num) ?_ ?_ ?_
  · exact mobiusHarmonicPair000_checked
  · exact mobiusHarmonicPair001_checked
  · rfl

#print axioms solution
