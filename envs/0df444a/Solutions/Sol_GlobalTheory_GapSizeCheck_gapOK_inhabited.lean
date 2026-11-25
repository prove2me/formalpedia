-- Prove2me | solution 1 for GlobalTheory.GapSizeCheck.gapOK_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:08.430046+00:00
-- url     : https://prove2.me/submissions/e80c9310-03e5-4cb9-90fc-ab996e0c5f22

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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) : ∃ h : ℝ, GapOK k r h := by
  set B : ℝ := |2 * Mexp r * (AS k r + AG k r) + AG k r + 3| +
    |9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3| +
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 with hB
  have hs : 1 ≤ 8 * Real.sqrt (2 * ((r : ℝ) + 1)) := by
    have : (1 : ℝ) ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
      rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
    linarith
  have h1 := abs_nonneg (2 * Mexp r * (AS k r + AG k r) + AG k r + 3)
  have h2 := abs_nonneg (9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3)
  have h3 : (0 : ℝ) ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
  have h1' := le_abs_self (2 * Mexp r * (AS k r + AG k r) + AG k r + 3)
  have h2' := le_abs_self (9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3)
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have ha : aOf r (B * (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) = B := by
    unfold aOf; field_simp
  refine ⟨B * (8 * Real.sqrt (2 * ((r : ℝ) + 1))), hk, ?_, ?_, ?_⟩
  · nlinarith
  · rw [ha]; linarith
  · rw [ha]; linarith
end GlobalTheory.GapSizeCheck
