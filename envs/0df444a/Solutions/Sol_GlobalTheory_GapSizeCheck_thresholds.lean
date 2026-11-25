-- Prove2me | solution 1 for GlobalTheory.GapSizeCheck.thresholds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:06.010851+00:00
-- url     : https://prove2.me/submissions/ceefb19f-7bc3-4700-aad4-c19cb295c8a8

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
theorem _root_.solution (k r : ℕ) (h : ℝ) (hg : GapOK k r h) :
    AG k r < (aOf r h - 1) / 2 ∧ AS k r < (aOf r h - 1) / 2 ∧
      (2 * Mexp r * AS k r + 1) + AG k r + 1 ≤ aOf r h - 1 := by
  obtain ⟨hk, -, h3, -⟩ := hg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hG0 : 0 ≤ AG k r := by unfold AG; positivity
  have hd0 : 0 ≤ dN k r := by unfold dN; nlinarith [mul_nonneg hr hk0]
  have hS0 : 0 ≤ AS k r := by unfold AS; positivity
  have hM : 2 ≤ Mexp r := by unfold Mexp; nlinarith
  have e1 : 2 * AS k r ≤ Mexp r * AS k r := mul_le_mul_of_nonneg_right hM hS0
  have e2 : 2 * AG k r ≤ Mexp r * AG k r := mul_le_mul_of_nonneg_right hM hG0
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith
end GlobalTheory.GapSizeCheck
