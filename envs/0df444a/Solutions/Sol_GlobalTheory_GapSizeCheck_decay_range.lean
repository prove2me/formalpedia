-- Prove2me | solution 1 for GlobalTheory.GapSizeCheck.decay_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:57.075275+00:00
-- url     : https://prove2.me/submissions/241c6d41-ca47-4ade-a070-5f69598eb09c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.ThreeDimData
open GlobalTheory GlobalTheory.GapSizeCheck
namespace GlobalTheory.GapSizeCheck
theorem _root_.solution (k r : ℕ) (h : ℝ) (h120 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : Real.sqrt ((r : ℝ) + 1) ≤ (r : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : (r : ℝ) + 1 ≤ n := by rw [hn]; push_cast; linarith
  have : ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) ≤ n * n :=
    mul_le_mul hn1 (hs.trans hn1) (Real.sqrt_nonneg _) (by linarith)
  nlinarith
end GlobalTheory.GapSizeCheck
