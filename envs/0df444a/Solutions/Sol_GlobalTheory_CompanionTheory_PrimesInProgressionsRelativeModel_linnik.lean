-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.linnik
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:35:16.60764+00:00
-- url     : https://prove2.me/submissions/5f8c04d7-4cfb-42d5-9073-0e656ea34108

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_linnik_of_relative_model

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
namespace GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
theorem _root_.solution (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompanionTheory.PrimesAP.linnik_of_relative_model h
  exact ⟨L, hL⟩
end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
