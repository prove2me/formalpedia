-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.add_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:51.776775+00:00
-- url     : https://prove2.me/submissions/2a41e802-5293-4e52-a722-0cad34502bcc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) (j : ℕ) : z + (j : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [add_re, natCast_re, zero_re] at h1
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith
end GlobalTheory.CompanionTheory.DigammaLimit
