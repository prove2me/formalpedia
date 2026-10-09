-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair063_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:18:51.797579+00:00
-- url     : https://prove2.me/submissions/94562d20-5e4d-409e-be13-7f2d22142fde

import Theorems.Thm_Helfgott_mobiusHarmonicBlock126_checked
import Theorems.Thm_Helfgott_mobiusHarmonicBlock127_checked
import Mathlib.Tactic

set_option autoImplicit false
namespace Helfgott

lemma harmonicPair063_mobiusTreeCheck_join (g : ℕ → ℤ) (B d offset : ℕ) (l r : MobiusCertTree)
    (hl : mobiusTreeCheck g B d offset l = true)
    (hr : mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true) :
    mobiusTreeCheck g B (d + 1) offset (.branch l r) = true := by
  by_cases hoff : B ≤ offset
  · simp [mobiusTreeCheck, hoff]
  · simpa [mobiusTreeCheck, hoff] using And.intro hl hr

lemma harmonicPair063_join (g M : ℕ → ℤ) (Q B d offset upper : ℕ)
    (l r : MobiusHarmonicTree) (hoff : offset < B)
    (hl : mobiusHarmonicTreeCheck g M Q B d offset l = true)
    (hr : mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true)
    (hu : upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r) :
    mobiusHarmonicTreeCheck g M Q B (d + 1) offset (.branch upper l r) = true := by
  have hoff' : ¬B ≤ offset := not_le.mpr hoff
  simpa [mobiusHarmonicTreeCheck, hoff', Bool.and_assoc, and_assoc] using ⟨hl, hr, hu⟩

end Helfgott
set_option Elab.async false
open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 1032192 (MobiusHarmonicTree.branch 3388947196 mobiusHarmonicBlock126 mobiusHarmonicBlock127) = true := harmonicPair063_join (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 8 1032192 3388947196 mobiusHarmonicBlock126 mobiusHarmonicBlock127 (by decide) mobiusHarmonicBlock126_checked mobiusHarmonicBlock127_checked (by decide +kernel)
#print axioms solution
